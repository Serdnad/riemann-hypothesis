module

public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle276
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle309
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle206
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle261
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle310
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle307
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_extend_of_dense {A E F : Type} [CommRing A] [CommRing E] [CommRing F] (ι : A →+* E) (f : A →+* F)
    (π P : A) (hf : IsUnit (f π)) (hP : f P = 0)
    (hd : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hs : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b, a = P * b) :
    ∃ g : E →+* F, (∀ a, g (ι a) = f a) := by
  first
  | exact @_root_.GlobalTheory.RelationExtension.exists_extension
  | exact _root_.GlobalTheory.RelationExtension.exists_extension
  | (apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationExtension.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationExtension.exists_extension ..)

theorem exists_letter_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W k _ _ lam hsurj hker hp
  let f : ZMod n → (LetA O n →+* k⸨X⸩) := fun i =>
    (algebraMap k⟦X⟧ k⸨X⸩).comp ((PowerSeries.map (algebraMap O k)).comp (Pi.evalRingHom (fun _ => O⟦X⟧) i))
  have hf : ∀ i (a : LetA O n), f i a = algebraMap k⟦X⟧ k⸨X⸩ (PowerSeries.map (algebraMap O k) (a i)) :=
    fun _ _ => rfl
  have hX : ∀ i, f i letπ = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := fun i => by
    rw [hf, letπ, PowerSeries.map_X]
  have hu : IsUnit (algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X) :=
    IsLocalization.map_units k⸨X⸩ (⟨PowerSeries.X, Submonoid.mem_powers _⟩ : Submonoid.powers (PowerSeries.X : k⟦X⟧))
  have hP : ∀ i, f i (PD.p : LetA O n) = 0 := fun i => by
    rw [map_natCast, ← map_natCast (algebraMap k k⸨X⸩), hp, map_zero]
  have hd : ∀ e : W.EE, ∃ (a : LetA O n) (m : ℕ) (y : W.EE), e * algebraMap (LetA O n) W.EE letπ ^ m =
      algebraMap (LetA O n) W.EE a + algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y := by
    intro e
    obtain ⟨a, m, h⟩ := W.EE_dense e 1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
    refine ⟨a, m, y, ?_⟩
    rw [map_pow, pow_one] at hy
    rw [map_natCast]
    linear_combination -hy
  have hs : ∀ (a : LetA O n) (y : W.EE), algebraMap (LetA O n) W.EE a =
      algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y → ∃ b, a = (PD.p : LetA O n) * b := by
    intro a y h
    have := W.EE_sat a 1 (Ideal.mem_span_singleton'.2 ⟨y, by rw [h, map_natCast, pow_one, mul_comm]⟩)
    simpa using this
  choose p hpa using fun i => exists_extend_of_dense (algebraMap (LetA O n) W.EE) (f i) letπ (PD.p : LetA O n)
    (by rw [hX]; exact hu) (hP i) hd hs
  obtain ⟨u, hπ⟩ := W.EE_π.exists_right_inv
  refine ⟨p, fun i a => hpa i a, fun i c => ?_, fun i e he => ?_⟩
  · obtain ⟨⟨s, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) c
    obtain ⟨t, rfl⟩ := PowerSeries.map_surjective _ hsurj s
    refine ⟨algebraMap (LetA O n) W.EE (fun _ => t) * u ^ m, ?_⟩
    have h1 := congrArg (p i) hπ
    rw [map_mul, hpa, hX, map_one] at h1
    simp only [map_pow] at h
    rw [map_mul, hpa, hf, map_pow, ← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  · obtain ⟨a, m, y, h⟩ := hd e
    have h1 := congrArg (p i) h
    rw [map_mul, he, zero_mul, map_add (f := _), map_mul, hpa, hpa, hP, zero_mul, add_zero, hf] at h1
    have h2 : PowerSeries.map (algebraMap O k) (a i) = 0 :=
      (IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [map_zero]; exact h1.symm)
    have h3 : ∀ j, ∃ d, PowerSeries.coeff j (a i) = lam * d := fun j => (hker _).1 (by
      have := congrArg (PowerSeries.coeff j) h2
      simpa using this)
    choose d hd' using h3
    obtain ⟨c, hc⟩ := (hker (PD.p : O)).1 (by rw [map_natCast, hp])
    have h4 : letE i * a = algebraMap O (LetA O n) lam * (letE i * fun _ => PowerSeries.mk d) := by
      funext j
      by_cases hj : j = i
      · subst hj
        ext l
        simp [letE, hd']
      · simp [letE, hj]
    have h5 : (PD.p : LetA O n) = algebraMap O (LetA O n) lam * algebraMap O (LetA O n) c := by
      rw [← map_mul, ← hc, map_natCast]
    have h6 := congrArg (algebraMap (LetA O n) W.EE) h4
    rw [h5] at h
    simp only [map_mul] at h h6
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
    have h7 : algebraMap (LetA O n) W.EE letπ ^ m * u ^ m = 1 := by rw [← mul_pow, hπ, one_pow]
    refine ⟨(algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (fun _ => PowerSeries.mk d) +
      algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) c) * y) * u ^ m, ?_⟩
    linear_combination (algebraMap (LetA O n) W.EE (letE i) * u ^ m) * h + u ^ m * h6 -
      (algebraMap (LetA O n) W.EE (letE i) * e) * h7

end GlobalTheory.RedFun
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.restriction_corestriction_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm20 D HW F := by
  first | exact @GlobalTheory.res_cor_H1f | exact GlobalTheory.res_cor_H1f | (intros; apply GlobalTheory.res_cor_H1f <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_semistable_tensor_pairing_of_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  first | exact @GlobalTheory.PMon.StPairing.exists_stPairing | exact GlobalTheory.PMon.StPairing.exists_stPairing | (intros; apply GlobalTheory.PMon.StPairing.exists_stPairing <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.EulerLevel

theorem card_H2_eq (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Nat.card (ReciprocityTheory.Gal.H2 rho) = Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual χ rho)) := by
  have hT := GlobalTheory.CocycleCount.card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have hA : Finite A := Subtype.finite
  rw [Nat.card_congr E]
  exact GlobalTheory.ZModDual.card_dual_eq N A



theorem core_pos (hT : Formalism.GaloisCohomology.LocalTateDualityK) (hE : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hG : GoodO (Qp := ℚ_[l]) LL O) (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hm : IsDualLat1 (P.PD K) LA LA' m) (r : ℕ) (hr : 0 < r) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (M : Type) [AddCommGroup M] (tM : TopologicalSpace M) (dM : @DiscreteTopology M tM) (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) :
    Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcM : Nat.card M = Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [← Nat.card_congr e.toEquiv]
    exact GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A LA r
  have hcM' : Nat.card (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) =
      Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL A.V) := by
    rw [GlobalTheory.T.card_lattice_quot_prime_pow l _ LL O hG A' LA' r, ← hm.1.2.2.2]
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hcM]; exact pow_ne_zero _ hcO)
  have htor : ∀ x : M, l ^ r • x = 0 := by
    intro x
    rw [← e.apply_symm_apply x, ← map_nsmul]
    generalize e.symm x = y
    induction y using Submodule.Quotient.induction_on with
    | H t =>
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).2, map_zero]
      rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  haveI instM : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule htor
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  have hφ1 : φ.symm 1 = 1 := map_one _
  have hφm : ∀ g h, φ.symm (g * h) = φ.symm g * φ.symm h := map_mul _
  have hact1 : ∀ x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), actQ LA _ hI 1 x = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ 1 (t : A.V) = t
        rw [map_one]
        rfl))
  have hactm : ∀ (g h : ↥(GK K)) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))),
      actQ LA _ hI (g * h) x = actQ LA _ hI g (actQ LA _ hI h x) := by
    intro g h x
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      exact congrArg Submodule.Quotient.mk (Subtype.ext (by
        show A.ρ (g * h) (t : A.V) = A.ρ g (A.ρ h t)
        rw [map_mul]
        rfl))
  have hex : ∃ rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M,
      ∀ (g : Formalism.GaloisCohomology.GK l K.1) (x : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))), rho g (e x) = e (actQ LA _ hI (φ.symm g) x) :=
    ⟨GlobalTheory.CocycleCount.repOfAction _
      (fun g => e.toAddMonoidHom.comp ((actQ LA _ hI (φ.symm g)).toAddMonoidHom.comp e.symm.toAddMonoidHom))
      (fun x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφ1, hact1, AddEquiv.apply_symm_apply])
      (fun g h x => by
        simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
          AddEquiv.coe_toAddMonoidHom, hφm, hactm, AddEquiv.symm_apply_apply]),
      fun g x => congrArg (fun y => e (actQ LA _ hI (φ.symm g) y)) (e.symm_apply_apply x)⟩
  obtain ⟨rho, hcomp⟩ := hex
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun x => ?_
    have hx : (fun g => rho g x) = fun g => e (actQ LA _ hI (φ.symm g) (e.symm x)) := by
      funext g
      rw [← hcomp, e.apply_symm_apply]
    rw [hx]
    exact ((GlobalTheory.T.lattice_modPow_action_isLocallyConstant l ↥(GK K) LL O hG A LA r hI (e.symm x)).comp e).continuous.comp hφ.2
  have hT1 := hT l K.1 hK r M rho hr hrho
  obtain ⟨⟨eH⟩, -, -, -, hb⟩ := hT1
  have hEu := hE l K.1 hK r M rho hr hrho
  have hTr := GlobalTheory.T.card_H1_H0_transport_lattice l K LL O A LA _ hI (l ^ r) M e rho hcomp
  obtain ⟨h1Q, h0Q⟩ := hTr
  have hTDfin : Finite (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) :=
    (GlobalTheory.CocycleCount.card_linear_le (l ^ r) M).1
  have hH2 := card_H2_eq (l ^ r) _ M _ rho eH hb
  have hD := GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff l LL O hG
  obtain ⟨lam, hlam⟩ := hD
  have hMp := GlobalTheory.T.tracePairing_injective_equivariant_levelMap l P K LL O A A' LA LA' m hm lam hlam r hI hI' (GlobalTheory.T.periodCyclotomicChar_reduces_mod_prime_pow l P K r) M e rho hcomp
  obtain ⟨Ψ, hΨi, hΨe⟩ := hMp
  have hcD : Nat.card (ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M) = Nat.card M :=
    GlobalTheory.ZModDual.card_dual_eq (l ^ r) M
  have hΨb : Function.Bijective Ψ :=
    hΨi.bijective_of_nat_card_le (by rw [hcD, hcM, hcM'])
  have hfix' : Nat.card {y : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) // ∀ g, actQ LA' _ hI' g y = y} =
      Nat.card (ReciprocityTheory.Gal.H0 (ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho)) := by
    refine Nat.card_congr ((Equiv.ofBijective _ hΨb).subtypeEquiv fun y => ?_)
    rw [Equiv.ofBijective_apply, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro hy g
      exact (hΨe g y).symm.trans (congrArg Ψ (hy _))
    · intro hy g
      have h := hΨe (φ g) y
      have h2 : (IntermediateField.fixingSubgroupEquiv K.1).symm (φ g) = g := φ.symm_apply_apply g
      rw [h2, hy (φ g)] at h
      exact hΨb.1 h
  rw [h1Q, hEu, ← h0Q, hH2, ← hfix', hcM, ← pow_mul]
  rw [show r * finrank LL A.V * finrank ℚ_[l] ↥K.1 = r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V) by ring]

theorem card_H1Q_eq : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  intro hT hE l _ P K LL _ _ _ O _ _ hG A A' LA LA' m hm r hI hI'
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hp : l.Prime := Fact.out
  obtain ⟨-, -, hfinO, -⟩ := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hG
  have hcO : Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ≠ 0 := by
    have := hfinO 1
    rw [pow_one] at this
    exact Nat.card_pos.ne'
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hs : ∀ (X : Type) [AddCommGroup X] [Module O X],
        Subsingleton (X ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O X)) := by
      intro X _ _
      rw [Submodule.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one, Submodule.top_smul]
    haveI := hs ↥LA.T
    haveI := hs ↥LA'.T
    have e1 : Nat.card (QuotientCohomology LA _ hI) = 1 := by
      haveI : Subsingleton (QuotientCohomology LA _ hI) := (Submodule.Quotient.mk_surjective _).subsingleton
      exact Nat.card_unique
    have e2 : Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} = 1 := by
      haveI : Unique {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    have e3 : Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} = 1 := by
      haveI : Unique {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ 0} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} :=
        { default := ⟨0, fun g => map_zero _⟩, uniq := fun _ => Subsingleton.elim _ _ }
      exact Nat.card_unique
    simp only [e1, e2, e3]
    simp
  · exact core_pos hT hE l P K LL O hG A A' LA LA' m hm r hr hI hI' _ ⊥ (@DiscreteTopology.mk _ ⊥ rfl) (AddEquiv.refl _)

end GlobalTheory.EulerLevel
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFiniteH1

theorem tate_finH1 (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO A LA
  obtain ⟨hR, hRs⟩ := GlobalTheory.T.goodCoefficients_explicit_sums l LL O hO
  haveI : Module.Free O ↥LA.T := LA.free
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  obtain ⟨hTc, hTs⟩ := GlobalTheory.T.free_finite_module_adicComplete_and_separated ((l : ℕ) : O) hR hRs ↥LA.T
  have hmemT : ∀ c : ↥(latticeCocycles LA), ∀ g, (c : ↥(GK K) → A.V) g ∈ LA.T := fun c g =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 c.2).2) g (Set.mem_univ g)
  have hd : ∀ t : ↥LA.T, ((cob A.ρ).restrictScalars O) (t : A.V) ∈ latticeCocycles LA := fun t => by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => ?_⟩
    · change Continuous fun g => A.ρ g (t : A.V) - (t : A.V)
      simp only [sub_eq_add_neg]
      exact (A.cont _).add continuous_const
    · change A.ρ (g * h) (t : A.V) - (t : A.V) = (A.ρ g (t : A.V) - (t : A.V)) + A.ρ g (A.ρ h (t : A.V) - (t : A.V))
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    · change A.ρ g (t : A.V) - (t : A.V) ∈ LA.T
      exact LA.T.sub_mem (LA.stable g _ t.2) t.2
  let d : ↥LA.T →ₗ[O] ↥(latticeCocycles LA) :=
    LinearMap.codRestrict (latticeCocycles LA) (((cob A.ρ).restrictScalars O).comp LA.T.subtype) hd
  have hdN : LinearMap.range d ≤ (latticeCoboundaries LA).comap (latticeCocycles LA).subtype := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, t.2, rfl⟩
  have hZ : ∀ c : ↥(latticeCocycles LA), (∀ n : ℕ, ∃ z : ↥(latticeCocycles LA), c = ((l : ℕ) : O) ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext
    funext g
    have h0 := hTs ⟨_, hmemT c g⟩ fun n => by
      obtain ⟨z, hz⟩ := hc n
      refine ⟨⟨_, hmemT z g⟩, Subtype.ext ?_⟩
      change (c : ↥(GK K) → A.V) g = ((l : ℕ) : O) ^ n • (z : ↥(GK K) → A.V) g
      rw [hz]
      rfl
    exact congrArg Subtype.val h0
  obtain ⟨s, hs⟩ := GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime hT l K LL O hO A LA
  refine GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range ((l : ℕ) : O) hR hTc hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', hm⟩ := hs c
  obtain ⟨x, hx, hxe⟩ := hm
  refine ⟨a, c', ⟨x, hx⟩, Subtype.ext ?_⟩
  have e : ((d ⟨x, hx⟩ : ↥(latticeCocycles LA)) : ↥(GK K) → A.V) = ((cob A.ρ).restrictScalars O) x := rfl
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, e, hxe]
  abel

end GlobalTheory.TateFiniteH1
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem finite_H1Q_lpow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA r hI
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hrest⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl : ((l : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h0, map_zero]
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] LL)] at h1
    have h2 : ((l : ℕ) : ℚ_[l]) = 0 := (algebraMap ℚ_[l] LL).injective (by rw [h1, map_zero])
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero r hl) hϖ
  have hspan : Ideal.span {((l : ℕ) : O) ^ r} = Ideal.span {ϖ ^ m} :=
    Ideal.span_singleton_eq_span_singleton.2 hm
  have key : ∀ (I : Submodule O ↥LA.T) (hI' : StableSub LA I),
      I = (Ideal.span {ϖ ^ m} • ⊤ : Submodule O ↥LA.T) → Finite (QuotientCohomology LA I hI') := by
    rintro I hI' rfl
    have hZ := finite_Z1Q hT l K LL O hO A LA ϖ hϖ m hI'
    have : Finite ↥(quotientCocycles LA _ hI') := hZ.to_subtype
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact key _ hI (by rw [hspan])

end GlobalTheory.CocycleModPow
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  first | exact @GlobalTheory.CocycleModPow.finite_Z1Q | exact GlobalTheory.CocycleModPow.finite_Z1Q | (intros; apply GlobalTheory.CocycleModPow.finite_Z1Q <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.H1_lattice_rank_growth_of_goodO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA) → Module.Finite LL (H1V A.ρ) ∧ ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) ≤ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ∧ Nat.card (LatticeCohomology LA ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA))) ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL (H1V A.ρ)) := by
  first | exact @GlobalTheory.H1Rank.growth_H1T_dim_H1V | exact GlobalTheory.H1Rank.growth_H1T_dim_H1V | (intros; apply GlobalTheory.H1Rank.growth_H1T_dim_H1V <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isDeRham_of_invertible_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.PMon.isDR_of_periodMatrix | exact GlobalTheory.PMon.isDR_of_periodMatrix | (intros; apply GlobalTheory.PMon.isDR_of_periodMatrix <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.ker_reduction_H1_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), ∃ f : LatticeCohomology LA →ₗ[O] QuotientCohomology LA _ hI, LinearMap.ker f = (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O (LatticeCohomology LA)) ∧ ∀ d : ↥(latticeCocycles LA), ∃ h : redT LA _ d ∈ quotientCocycles LA _ hI, f (Submodule.Quotient.mk d) = Submodule.Quotient.mk ⟨redT LA _ d, h⟩ := by
  first | exact @GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | exact GlobalTheory.ReductionH1Kernel.ker_reduction_H1 | (intros; apply GlobalTheory.ReductionH1Kernel.ker_reduction_H1 <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' : ∀ (l : ℕ) [Fact l.Prime] (H : ℕ) (ζ : PadicComplex l), IsPrimitiveRoot ζ (l ^ (1 + n0 l H)) → ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | exact GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | (intros; apply GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

theorem _root_.GlobalTheory.T.exists_mem_span_corner_charpoly_separable : ∀ {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ} (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), AbsIrrDistinct (matRep σ) → b * a = 1 → a * b ∈ Submodule.span K (Set.range σ) → ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_mem_span_corner_separable | exact GlobalTheory.SpanRing.exists_mem_span_corner_separable | (intros; apply GlobalTheory.SpanRing.exists_mem_span_corner_separable <;> assumption)
end
