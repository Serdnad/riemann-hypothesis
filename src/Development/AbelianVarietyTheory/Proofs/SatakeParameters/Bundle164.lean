module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_lift_levels_good_primes_properties : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.Q A.μ0 = ∅ ∧ (∀ t P, Good R t P → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ Good R t (_root_.Formalism.DivisionValues.conjPl P) ∧ Good R A.μ0 P) ∧ (∀ SF, IsSF R SF → ∀ P, OffS D SF P ↔ Good R A.μ0 P) ∧ (R.IsFam → ∀ t, ∀ P ∈ A.ok t, Good R t (R.pl P) ∧ _root_.Formalism.DivisionValues.conjPl (R.pl P) ≠ R.pl P ∧ A.q P = Ideal.absNorm (R.pl P).asIdeal) := by
  first | exact @GlobalTheory.GoodPrimes.good_primes | exact GlobalTheory.GoodPrimes.good_primes | (intros; apply GlobalTheory.GoodPrimes.good_primes <;> assumption)
end

section


theorem _root_.GlobalTheory.T.cayleyTransform_trivial_phase_skewHermitian : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1) →
    ∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1 := by
  first | exact @GlobalTheory.Hk3.CayleyPhase.cayley_phase | exact GlobalTheory.Hk3.CayleyPhase.cayley_phase | (intros; apply GlobalTheory.Hk3.CayleyPhase.cayley_phase <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.locPair_vacuum_relation_independent : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, s ≠ 0 → LocVac ρ s → (c.sum fun x z => z • ρ x s) = 0 → ∀ s', LocVac ρ s' → (c.sum fun x z => z • ρ x s') = 0 := by
  first | exact @GlobalTheory.Hk3.locVac_rel_indep | exact GlobalTheory.Hk3.locVac_rel_indep | (intros; apply GlobalTheory.Hk3.locVac_rel_indep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOffLevels

open GlobalTheory.IdemSupport GlobalTheory.ResLoc Formalism.L2.JoinChr

theorem exists_glue {A : Type} [CommRing A] {e : A} (he : e * e = e) (x : Aˣ) :
    ∃ y : Aˣ, (y : A) = e * (x : A) + (1 - e) ∧ e * ((y : A) - 1) = (y : A) - 1 := by
  have hxx : (x : A) * ((x⁻¹ : Aˣ) : A) = 1 := Units.mul_inv x
  refine ⟨⟨e * (x : A) + (1 - e), e * ((x⁻¹ : Aˣ) : A) + (1 - e), ?_, ?_⟩, rfl, ?_⟩
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · linear_combination (e * e) * hxx + (2 - (x : A) - ((x⁻¹ : Aˣ) : A)) * he
  · change e * (e * (x : A) + (1 - e) - 1) = e * (x : A) + (1 - e) - 1
    linear_combination ((x : A) - 1) * he

variable {D : D7}



theorem exists_part {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (hu : χ.UnrAt P)
    {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D} (hd : IsDelta Φ P e) (hpl : IsPlIdem D e P)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ c y = 1 := by
  obtain ⟨d0, d1, d2⟩ := id hd
  have he : e * e = e := hpl.1
  obtain ⟨N, hN, hker⟩ := exists_modulus hΦ c hc.1.1
  obtain ⟨y, hy, hsupp⟩ := exists_glue he x
  have hyP : Φ (y : AE D) P = Φ (x : AE D) P := by
    rw [hy, ev_add, ev_mul, d1, one_mul, ev_sub, ev_one, d1, sub_self, add_zero]
  have hv : Valued.v (Φ (x : AE D) P) = 1 := by
    have a : Valued.v (Φ (x : AE D) P) ≤ 1 := (hΦ.int _).1 h1 P
    have b : Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) ≤ 1 := (hΦ.int _).1 h2 P
    have ab : Valued.v (Φ (x : AE D) P) * Valued.v (Φ ((x⁻¹ : (AE D)ˣ) : AE D) P) = 1 := by
      rw [← map_mul, ← ev_mul, Units.mul_inv, ev_one, map_one]
    refine le_antisymm a ?_
    rw [← ab]
    exact mul_le_of_le_one_right' b
  have hy1 : Valued.v (Φ (y : AE D) P) = 1 := by rw [hyP, hv]
  obtain ⟨k, k1, k2, k3⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (Φ (y : AE D) P) (fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1)
  rw [hy1] at k1
  rw [← k1, mul_one] at k2 k3
  obtain ⟨l, hl⟩ : ∃ l : (AE D)ˣ, (l : AE D) = 1 + e * (incA D (k : D.host.E) - 1) := ⟨locU hpl.1 k, rfl⟩
  obtain ⟨z, hz, hz'⟩ := exists_units_quot y l hl
  have hyz : Φ (y : AE D) P = Φ (z : AE D) P * algebraMap D.host.E _ (k : D.host.E) := by
    rw [← ev_inc hΦ]
    exact map_eq_mul_of_supp (evAt Φ P) d1 hz'
  have hcz : c z = 1 := by
    refine hker P z (map_eq_one_of_supp (infPart D) d0 hsupp hz')
      (fun Q hQ => map_eq_one_of_supp (evAt Φ Q) (d2 Q hQ) hsupp hz') ?_ ?_
    · rwa [hyz, map_mul, val_alg, ← k1, mul_one] at hy1
    · rwa [hyz, ← sub_one_mul, map_mul, val_alg, ← k1, mul_one] at k2
  have hcl : c l = 1 := by
    have e1 := hc.2 P e hpl k l hl
    have e2 : χ.locK P k = 1 := by
      refine hu (Formalism.L2.Host.atFin P k) ?_
      change Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [val_alg]
      exact k1.symm
    rw [e2, Units.val_one] at e1
    exact Circle.ext e1
  exact ⟨y, hy, by rw [hz, map_mul, hcz, hcl, one_mul]⟩

theorem unrPl_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) {P : Pl D.host.E} (h : χ.UnrAt P)
    (h' : χ.UnrAt (Formalism.DivisionValues.conjPl P)) : UnrPl P c := by
  intro e f hp x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd : IsDelta Φ P e := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, ⟨v, ε, hε, he⟩, ht⟩
  · have hc' : Formalism.IndefR.Lev.IsConjPl P (Formalism.DivisionValues.conjPl P) := GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl
    have hi' : Formalism.L2.NTheta.IsIdemAt (cA D e) (Formalism.DivisionValues.conjPl P) :=
      (supported_group_and_prime_idempotents (D.sp.V 0)).2.2.2 P _ e hi hc'
    have hd' : IsDelta Φ (Formalism.DivisionValues.conjPl P) (cA D e) := delta_of_isIdemAt hΦ hi'
    have pl : ∀ {w : Pl D.host.E} {a : AE D}, Formalism.L2.NTheta.IsIdemAt a w → IsPlIdem D a w := fun ha => by
      obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := ha
      exact ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩
    obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd (pl hi) x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_part hc h' hΦ hd' (pl hi') x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_part hc h hΦ hd ⟨delta_idem hΦ hd, ⟨v, ε, hε, Or.inr he⟩, ht⟩ x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

theorem unrPl_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → ∀ t P, Good R t P → UnrPl P R.eta ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → UnrPl P (R.toLevCh.mu t j) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL t P hP
  obtain ⟨hg, hc, -⟩ := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t P hP
  have hg' := (GlobalTheory.GoodPrimes.good_primes R F hL).2.1 t _ hc
  have hμ : ∀ w, Good R t w → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ∀ k, (hk : k < D.R.m) →
      (R.C.mu0 ⟨k, hk⟩).UnrAt w ∧ (R.xiH t).UnrAt w := fun w hw hgw k hk => by
    refine ⟨(R.C.isMu0 _).unr w fun i hi => ?_, ?_⟩
    · have hi' : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := hi
      refine hgw ?_
      rw [Nat.cast_mul]
      fin_cases i
      · exact Ideal.mul_mem_right _ _ hi'
      · exact Ideal.mul_mem_left _ _ hi'
    · by_contra h
      rcases (hL.Q_ram t w).1 h with h | ⟨PP, h, hc⟩
      · exact (hw w (Or.inr h)).1 rfl
      · exact (hw PP (Or.inr h)).2 hc
  refine ⟨unrPl_of_chrEq hL.eta (R.C.isEta.unr _) (R.C.isEta.unr _), fun j h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have a := unrPl_of_chrEq (hL.mu0 ⟨k, h2⟩) (hμ P hP hg k h2).1 (hμ _ hc hg'.1 k h2).1
  have b := unrPl_of_chrEq (hL.xi t) (hμ P hP hg k h2).2 (hμ _ hc hg'.1 k h2).2
  intro e f h x x1 x2 x3
  show R.mu0 (k + 1) x * R.xi t x = 1
  rw [a e f h x x1 x2 x3, b e f h x x1 x2 x3, one_mul]

end GlobalTheory.UnrOffLevels
end

section

noncomputable section

namespace GlobalTheory.TwV.Xc.Unif

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV
  Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

section OneAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneAt (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) : AfE F E :=
  Formalism.UG.P.afsplitIE w a + (1 - Formalism.UG.P.afsplitEps E w)

theorem prV_oneAt_self (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w (oneAt w a) = a := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE, Formalism.UG.P.afsplit_prV_eps, sub_self, add_zero]

theorem prV_oneAt_ne (w w' : HeightOneSpectrum (𝓞 F)) (h : w' ≠ w) (a : E ⊗[F] w.adicCompletion F) :
    prV (E := E) w' (oneAt w a) = 1 := by
  rw [oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_prV_IE_ne w w' h, Formalism.UG.P.afsplit_prV_eps_ne w w' h,
    sub_zero, zero_add]

theorem ext_prV {x y : AfE F E} (h : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w x = prV (E := E) w y) : x = y := by
  rw [← sub_eq_zero]
  exact Formalism.UG.P.afsplit_inj _ fun w => by rw [map_sub, h, sub_self]

theorem oneAt_mul (w : HeightOneSpectrum (𝓞 F)) (a b : E ⊗[F] w.adicCompletion F) :
    oneAt w a * oneAt w b = oneAt w (a * b) := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [map_mul, prV_oneAt_self, prV_oneAt_self, prV_oneAt_self]
  · rw [map_mul, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, prV_oneAt_ne w w' h, one_mul]

theorem oneAt_one (w : HeightOneSpectrum (𝓞 F)) : oneAt (E := E) w 1 = 1 := ext_prV fun w' => by
  by_cases h : w' = w
  · subst h; rw [prV_oneAt_self, map_one]
  · rw [prV_oneAt_ne w w' h, map_one]

theorem sigR_oneAt (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] w.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w a) = oneAt w (sigR σ (w.adicCompletion F) a) := by
  rw [oneAt, oneAt, map_add (f := _), map_sub, map_one, Formalism.UG.P.afsplit_sigR_IE, Formalism.UG.P.afsplit_sigR_eps]

def oneAtU (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) : (AfE F E)ˣ :=
  ⟨oneAt w a, oneAt w (a⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ),
    by rw [oneAt_mul, Units.mul_inv, oneAt_one], by rw [oneAt_mul, Units.inv_mul, oneAt_one]⟩

theorem oneAtU_coe (w : HeightOneSpectrum (𝓞 F)) (a : (E ⊗[F] w.adicCompletion F)ˣ) :
    (oneAtU w a : AfE F E) = oneAt w a := rfl

end OneAt

theorem exists_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) [Fact p.Prime],
    LocGood σ J A → ∀ v, ∃ π ∈ U1 σ, OneOff (A.pl v).1 π ∧ ordA A v π = 1 := by
  intro F E _ _ _ _ _ σ n p G A J _ H v
  have hp0 : (p : (A.pl v).1.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F ((A.pl v).1.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  let c : ((A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F)ˣ :=
    ⟨((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹),
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)),
      Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0), Prod.ext (inv_mul_cancel₀ hp0) (mul_inv_cancel₀ hp0)⟩
  let a : (E ⊗[F] (A.pl v).1.adicCompletion F)ˣ := Units.map (A.spl v).symm.toMonoidHom c
  have ha : A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F) =
      ((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) := by
    show A.spl v ((A.spl v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
  refine ⟨oneAtU (A.pl v).1 a, ?_, fun w' hw' => prV_oneAt_ne _ w' hw' _, ?_⟩
  · rw [U1, MonoidHom.mem_ker]
    apply Units.ext
    show oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt (A.pl v).1 (a : E ⊗[F] (A.pl v).1.adicCompletion F)) = 1
    rw [sigR_oneAt, oneAt_mul, ← oneAt_one (E := E) (A.pl v).1]
    congr 1
    apply (A.spl v).injective
    rw [map_mul, H.sig v, ha, map_one]
    show (((p : (A.pl v).1.adicCompletion F), (p : (A.pl v).1.adicCompletion F)⁻¹) *
      ((p : (A.pl v).1.adicCompletion F)⁻¹, (p : (A.pl v).1.adicCompletion F)) :
        (A.pl v).1.adicCompletion F × (A.pl v).1.adicCompletion F) = 1
    exact Prod.ext (mul_inv_cancel₀ hp0) (inv_mul_cancel₀ hp0)
  · have := (G.P.setting v).frac_alt
    have hp := (G.P.setting v).p_unif
    have h1 := ordP_eq (Qq := G.P.Qq v) hp 1 1
    have h2 : phiA A v (oneAtU (A.pl v).1 a : AfE F E) = (p : G.P.Qq v) := by
      simp only [phiA, RingHom.comp_apply, oneAtU_coe, prV_oneAt_self]
      show (A.eQ v).symm ((A.spl v (a : E ⊗[F] (A.pl v).1.adicCompletion F)).1) = _
      rw [ha, map_natCast]
    unfold ordA
    rw [h2]
    simpa using h1

end GlobalTheory.TwV.Xc.Unif

end
end

section

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem int_of_psi_trace_gam : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k
  have hσ := hU.1
  have hv := hU.2.1
  have hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L := by
    refine GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)
    set c : L := b * ϖ ^ max (e j) (e k) with hc
    have hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k) := by
      rw [hc, map_mul, map_pow]
      exact mul_le_of_le_one_left' hb
    have hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e := by
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, map_add (f := _), apply_ite σ, map_neg, hσ, map_zero,
          and_comm (a := k = a'), and_comm (a := j = a')]
        split_ifs <;> ring
      · rw [Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [max_comm]; exact hcv
          · simp
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [Valuation.map_neg, hv]; exact hcv
          · simp
    have h := hψ _ hmem
    have e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k) := by rw [hc]; ring
    rw [e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]
    congr 1
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul] at hw
  exact hw

end GlobalTheory.Hk3.GramSep
end

section

open Matrix

theorem _root_.GlobalTheory.T.vacuumPhase_sub_trace_mem_integers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | exact GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem | (intros; apply GlobalTheory.Hk3.VacPhase.locH_sub_trace_mem <;> assumption)
end

section

namespace GlobalTheory.Hk3

theorem locVac_span_classes_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]
  set Λ := HoweDuality.intMat L n' n with hΛdef

  have hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤
      fun c => Submodule.span ℂ {ρ c.out s} := by
    intro c
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, rfl⟩
    have hm : -c.out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])
    have := hshift s hvac c.out _ hm
    rw [add_neg_cancel_left] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine iSupIndep.mono ?_ hle
  by_cases hs : s = 0
  · have hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥ := by
      funext c; rw [hs, map_zero, Submodule.span_singleton_eq_bot]
    rw [hb, iSupIndep_def]
    intro i
    exact disjoint_bot_left
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)
  refine LinearIndependent.iSupIndep_span_singleton ?_
  rw [linearIndependent_iff']
  intro I C hC y hy
  have hind := eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L))
    (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') =>
      ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
    (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
    (by
      intro y _ y' _ hyy
      by_contra hcon
      push_neg at hcon
      apply hyy
      have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
      rw [hΛ] at hm
      rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
      exact hm)
    C hC
  exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)

end GlobalTheory.Hk3
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  first | exact @GlobalTheory.HeckeFinTriv.finPart_eq_one | exact GlobalTheory.HeckeFinTriv.finPart_eq_one | (intros; apply GlobalTheory.HeckeFinTriv.finPart_eq_one <;> assumption)
end
