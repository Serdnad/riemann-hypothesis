module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AbsoluteLogMeanBounds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle069
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle072
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Proof.CosetGroupEquiv

open NumberField IsDedekindDomain Formalism.UG Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

section Abstract

variable {G : Type} [Group G]

def cosetGrpEquiv (Γ K : Subgroup G) (y : G) : CosetGroupMembership.cosetGrp Γ K y ≃ stabAt Γ K y where
  toFun x := ⟨⟨x.1, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).1⟩, ((CosetGroupMembership.mem_cosetGrp Γ K y x.1).1 x.2).2⟩
  invFun x := ⟨x.1.1, (CosetGroupMembership.mem_cosetGrp Γ K y x.1.1).2 ⟨x.1.2, x.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_cosetGrp (Γ K : Subgroup G) (y : G) :
    Nat.card (CosetGroupMembership.cosetGrp Γ K y) = Nat.card (stabAt Γ K y) :=
  Nat.card_congr (cosetGrpEquiv Γ K y)

theorem sum_clause_iff (Γ K : Subgroup G) (m : ℝ) :
    (∀ (ι : Type) [Fintype ι] (y : ι → G),
      Function.Bijective (fun i => (DoubleCoset.mk Γ K (y i) : ClassSet Γ K)) →
      ∑ i, ((Nat.card (CosetGroupMembership.cosetGrp Γ K (y i)) : ℕ) : ℝ)⁻¹ = m) ↔
    (∀ [Fintype (ClassSet Γ K)] (s : ClassSet Γ K → G), (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      ∑ c, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹ = m) := by
  constructor
  · intro h _ s hs
    have hb : Function.Bijective (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) := by
      have : (fun c => (DoubleCoset.mk Γ K (s c) : ClassSet Γ K)) = id := funext hs
      rw [this]
      exact Function.bijective_id
    rw [← h _ s hb]
    simp only [card_cosetGrp]
  · intro h ι _ y hy
    let e : ι ≃ ClassSet Γ K := Equiv.ofBijective _ hy
    letI : Fintype (ClassSet Γ K) := Fintype.ofEquiv ι e
    have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (y (e.symm c)) = c := fun c => e.apply_symm_apply c
    rw [← h (fun c => y (e.symm c)) hs, ← e.symm.sum_comp]
    simp only [card_cosetGrp]

theorem cosetSum_iff (Γ K : Subgroup G) (m : ℝ) : CosetGroupMembership.CosetSum Γ K m ↔ ClassesDoubleCosets.CosetMass Γ K m :=
  and_congr Iff.rfl (and_congr (forall_congr' fun y => (cosetGrpEquiv Γ K y).finite_iff)
    (sum_clause_iff Γ K m))

end Abstract

section Obj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stabHat_eq (hc : CMData F E) (S : HSpace E) (N : Submodule (𝓞 E) S.V) :
    CosetGroupMembership.stabHat hc S N = ClassesDoubleCosets.stabHat hc S N := rfl

theorem stabHat0_eq {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) :
    CosetGroupMembership.stabHat0 sp N = (levelAfL sp.cm.sig sp.gram0 (sp.crdLat0 N)).subgroupOf
      (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)) := by
  ext x
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

def InCoords (hc : CMData F E) {k : ℕ} (J : Matrix (Fin k) (Fin k) E) (Λ : Submodule (𝓞 E) (Fin k → E))
    (m : ℝ) : Prop :=
  CosetGroupMembership.CosetSum ((ratPts hc.sig J (Af F)).subgroupOf (UPts hc.sig J (Af F)))
    ((stabGL (hatL (F := F) Λ)).subgroupOf (UPts hc.sig J (Af F))) m

theorem inCoords_cast (hc : CMData F E) (S : HSpace E) {k : ℕ} (h : S.rank = k) (N : Submodule (𝓞 E) S.V)
    (m : ℝ) :
    InCoords hc S.gram (crdLat S N) m ↔
    InCoords hc (S.gram.reindex (finCongr h) (finCongr h))
      (N.map (((S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm) :
        S.V ≃ₗ[E] (Fin k → E)) : S.V →ₗ[E] (Fin k → E)).restrictScalars (𝓞 E))) m := by
  subst h
  rfl

theorem general_clause_iff {R : Ranks} (sp : Spaces R F E) (N : Submodule (𝓞 E) (sp.X 0).V) (m : ℝ) :
    CosetGroupMembership.CosetSum (UFin sp.cm (sp.X 0)) (CosetGroupMembership.stabHat sp.cm (sp.X 0) N) m ↔
    CosetGroupMembership.CosetSum (CosetGroupMembership.rat0 sp) (CosetGroupMembership.stabHat0 sp N) m :=
  inCoords_cast sp.cm (sp.X 0) sp.rank0 N m

end Obj

theorem general_iff : CosetGroupMembership.GeneralForm ↔ ClassesDoubleCosets.General := by
  unfold CosetGroupMembership.GeneralForm ClassesDoubleCosets.General
  simp only [cosetSum_iff, stabHat_eq]

theorem column_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    CosetGroupMembership.ColumnForm D ↔ ClassesDoubleCosets.DefiniteSpaceClassStatement D Lv u := by
  letI := D.host.cmStar
  unfold CosetGroupMembership.ColumnForm ClassesDoubleCosets.DefiniteSpaceClassStatement
  refine forall_congr' fun N => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [cosetSum_iff, stabHat0_eq]
  rfl

theorem column_of_general (h : CosetGroupMembership.GeneralForm) (D : D7) : CosetGroupMembership.ColumnForm D := by
  letI := D.host.cmStar
  intro N hN hU
  exact (general_clause_iff D.sp N _).1
    (h D.host.F D.host.E D.sp.cm (D.sp.X 0) (D.sp.X_sig 0) (baseSpace_posDef D.R D.host.F D.sp) N hN hU)

theorem massAsCosetSum_iff : CosetGroupMembership.MassAsCosetSum ↔ ClassesDoubleCosets.ClassesAsDoubleCosets :=
  ⟨fun h => ⟨general_iff.1 h.1, fun D Lv u => (column_iff D Lv u).1 (h.2 D)⟩,
    fun h => ⟨general_iff.2 h.1, column_of_general (general_iff.2 h.1)⟩⟩

end GlobalTheory.Proof.CosetGroupEquiv

end
end

section

noncomputable section

namespace GlobalTheory.Theta0MeanCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem bound_eq (D : D7) : SignedLogMeans.bound D = AbsoluteLogMeanBounds.kronBound D := rfl

theorem one_le_d (D : D7) : (1 : ℝ) ≤ D.host.d := by
  have h := D.host.qd_big.2
  exact_mod_cast (by omega : 1 ≤ D.host.d)

theorem two_sqrt_le_rd (D : D7) : 2 * Real.sqrt D.host.d ≤ D.host.rdE := by
  refine le_trans ?_ (factRd D.R D.host).1
  have he : (2 : ℝ) ≤ D.R.e := by exact_mod_cast D.host.two_le_e
  have h1 : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

theorem one_le_sqrt_d (D : D7) : 1 ≤ Real.sqrt D.host.d := Real.one_le_sqrt.mpr (one_le_d D)

theorem kronBound_le (D : D7) {L : ℝ} (h : Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L) :
    AbsoluteLogMeanBounds.kronBound D ≤ L := by
  have h1 := two_sqrt_le_rd D
  have h2 := one_le_sqrt_d D
  have h3 : Real.log (Real.sqrt D.host.d) ≤ Real.log D.host.rdE :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 := Real.one_half_lt_eulerMascheroniConstant
  have h5 := le_abs_self (logDerivativeAtOne D)
  unfold AbsoluteLogMeanBounds.kronBound
  linarith

end GlobalTheory.Theta0MeanCompare
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicLatticeCompletion_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.LatLocGlob.latS_local_global | exact GlobalTheory.LatLocGlob.latS_local_global | (intros; apply GlobalTheory.LatLocGlob.latS_local_global <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  first | exact @GlobalTheory.OverCompare.exists_lattice_approx_all | exact GlobalTheory.OverCompare.exists_lattice_approx_all | (intros; apply GlobalTheory.OverCompare.exists_lattice_approx_all <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.localCharacter_ne_zero_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 → LocE.locChar (qOf P) cq χ a ≠ 0 := by
  first | exact @GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | exact GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero | (intros; apply GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.rationalFractions_represent_primeNormQuotient : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  first | exact @GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | exact GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps | (intros; apply GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

theorem _root_.GlobalTheory.T.latticeSandwich_of_latticeNormalForm : ∀ (X : Fields) (Pr : Primes X) (R : Ranks), GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.InclAt Pr R := by
  first | exact @GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | exact GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt | (intros; apply GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt <;> assumption)
end

section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.ExtLatMatrix

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (h : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1)
    {a : ℕ} (M : Submodule (𝓞 K) (Fin a → K)) (x : Fin a → K) (hx : x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M := by
  obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M x).1 hx
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have hs' : s = 0 := by exact_mod_cast h0
    rw [hs']
    exact w.asIdeal.zero_mem
  have hval : w.valuation K ((s : K)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have h1 : w.valuation K (s : K) = 1 := by
      rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs
    rw [h1, inv_one]
  have hint : σ ((s : K)⁻¹) ∈ v.integer := (h _).2 hval
  have hmem : (fun i => σ ((s • x) i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M :=
    Submodule.subset_span ⟨s • x, hsx, rfl⟩
  have hsm := Submodule.smul_mem _ (⟨σ ((s : K)⁻¹), hint⟩ : v.integer) hmem
  convert hsm using 1
  funext i
  change σ (x i) = σ ((s : K)⁻¹) * σ ((s : K) * x i)
  rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.extLat_matrix_integral : ∀ (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (σ : K →+* L), (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    (∀ (a : ℕ) (M : Submodule (𝓞 K) (Fin a → K)), ∀ x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M,
      (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) ∧
    ∀ (a b : ℕ) (M : Submodule (𝓞 K) (Fin a → K)) (MW : Submodule (𝓞 K) (Fin b → K))
      (B : GL (Fin a) K) (BW : GL (Fin b) K), _root_.Formalism.L2.DIV.IsBasisAt w M B → _root_.Formalism.L2.DIV.IsBasisAt w MW BW →
      ∀ ap : Matrix (Fin a) (Fin b) L,
        (∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW, ap *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) →
        ∀ i j, v ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap *
          (BW : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1 := by
  intro K _ _ w L Γ _ _ v σ h
  refine ⟨fun a M x hx => _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h M x hx, ?_⟩
  intro a b M MW B BW hB hBW ap hap i j
  have hunit : ∀ t : 𝓞 K, t ∉ w.asIdeal → v (σ ((t : K)⁻¹)) ≤ 1 := by
    intro t ht
    refine (h _).2 ?_
    rw [map_inv₀]
    have h1 : w.valuation K (t : K) = 1 := by
      rw [show (t : K) = algebraMap (𝓞 K) K t from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 ht
    rw [h1, inv_one]
  have hint : ∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M, ∀ k,
      v (((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ y) k) ≤ 1 := by
    intro y hy
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have hm' : m ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.colLat B) := by
        unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
        rw [← hB]
        exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hm
      obtain ⟨t, ht, htm⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal _ m).1 hm'
      unfold _root_.Formalism.L2.DIV.colLat at htm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 htm
      have ht0 : (t : K) ≠ 0 := by
        intro h0
        apply ht
        have ht' : t = 0 := by exact_mod_cast h0
        rw [ht']
        exact w.asIdeal.zero_mem
      have hBc : (B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K)) = (t : K) • m := by
        funext r
        have hr := congrFun hc r
        simp only [Finset.sum_apply, Pi.smul_apply] at hr
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [← Algebra.smul_def] at *
        convert hr using 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_def, mul_comm]
          try rfl
      have hBm : ((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m =
          (t : K)⁻¹ • fun k => (c k : K) := by
        have e : m = (t : K)⁻¹ • ((B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K))) := by
          rw [hBc, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        simp
      intro k
      have e : ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ (fun i => σ (m i))) k =
          σ ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m) k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e, hBm, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      refine mul_le_one' (hunit t ht) ((h _).2 ?_)
      exact HeightOneSpectrum.valuation_le_one w (c k)
    | zero => simp
    | add y z _ _ hy hz =>
      intro k
      rw [Matrix.mulVec_add, Pi.add_apply]
      exact v.map_add_le (hy k) (hz k)
    | smul c y _ hy =>
      intro k
      rw [Matrix.mulVec_smul, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      exact mul_le_one' c.2 (hy k)
  have hcol : (fun k => σ ((BW : Matrix (Fin b) (Fin b) K) k j)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW := by
    refine _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h MW _ ?_
    unfold _root_.Formalism.L2.DIV.IsBasisAt at hBW
    rw [hBW]
    exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have key := hint _ (hap _ hcol) i
  convert key using 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.ExtLatMatrix
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem smallPrimeOne_of_primesRel : GlobalTheory.Lin.PrimesRel → SmallPrimeOne := by
  intro h
  obtain ⟨C₀, Cr, cr, c, h0, h1, h2, h3, H⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel h
  obtain ⟨s, hsC, hs21, hsr⟩ : ∃ s : ℝ, C₀ ≤ s ∧ 21 ≤ s ∧ 200 * Cr / cr ≤ s :=
    ⟨max C₀ (max 21 (200 * Cr / cr)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _), le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hss : s ≤ s ^ 2 := by nlinarith
  have hexp : Cr * Real.exp (-cr * s) ≤ 1 / 200 := by
    have e1 : 200 * Cr ≤ cr * s := by
      rw [div_le_iff₀ h2] at hsr; linarith
    have e2 := Real.add_one_le_exp (cr * s)
    have e3 : 0 < Real.exp (cr * s) := Real.exp_pos _
    rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ e3 (by norm_num)]
    linarith
  refine ⟨3 * s ^ 2 + 1, by nlinarith, ?_⟩
  intro M hM
  rcases Nat.eq_or_lt_of_le hM with rfl | hM3
  · refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have e1 : ((2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (3 * s ^ 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    refine le_trans ?_ e1
    norm_num
  have hm3 : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hB0 : (0 : ℝ) < 4 * (M : ℝ) := by linarith
  have hB1 : (1 : ℝ) ≤ 4 * (M : ℝ) := by linarith
  have hlB : 1 ≤ Real.log (4 * (M : ℝ)) := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set Y : ℝ := (4 * (M : ℝ)) ^ (s ^ 2) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
  have hlY : Real.log Y = s ^ 2 * Real.log (4 * (M : ℝ)) := Real.log_rpow hB0 _
  have hlY2 : s ^ 2 ≤ Real.log Y := by rw [hlY]; nlinarith [sq_nonneg s]
  have hlY0 : 0 < Real.log Y := by linarith
  have hrho : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * M) Y ≤ 1 / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have a1 : Real.exp (-cr * Real.log Y / Real.log (4 * (M : ℝ))) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      rw [hlY, ← mul_assoc, mul_div_assoc, div_self (by linarith), mul_one]
      nlinarith
    have a2 : Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ Real.exp (-cr * s) := by
      apply Real.exp_le_exp.2
      have : s ≤ Real.sqrt (Real.log Y) := Real.le_sqrt_of_sq_le hlY2
      nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 h1.le
    have b2 := mul_le_mul_of_nonneg_left a2 h1.le
    linarith
  have h7 : (4 * (M : ℝ)) ^ (7 : ℝ) ≤ 1 * Y ^ ((1 : ℝ) / 3) := by
    rw [one_mul, hY, ← Real.rpow_mul hB0.le]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
  have hc := H M 1 hM3 (Nat.coprime_one_left M) Y 1
    (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) le_rfl hrho h7
  have hpos : 0 < c * 1 * (4 * (M : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y := by
    have := Real.rpow_pos_of_pos hB0 (-6 : ℝ)
    positivity
  have hcard := lt_of_lt_of_le hpos hc
  rw [Nat.cast_pos, Finset.card_pos] at hcard
  obtain ⟨p, hp⟩ := hcard
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨-, hp2⟩, hpp, hpm⟩ := hp
  refine ⟨p, hpp, ?_, ?_⟩
  · have : p % M = 1 % M := hpm
    rw [this]; exact Nat.mod_eq_of_lt (by omega)
  · have e1 : (p : ℝ) ≤ Y * (1 + 1) :=
      le_trans (Nat.cast_le.2 hp2) (Nat.floor_le (by positivity))
    have hM0 : (0 : ℝ) < M := by linarith
    have e2 : Y ≤ (M : ℝ) ^ (3 * s ^ 2) := by
      rw [Real.rpow_mul hM0.le]
      apply Real.rpow_le_rpow hB0.le _ (by positivity)
      have : (M : ℝ) ^ (3 : ℝ) = (M : ℝ) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (M : ℝ) 3
      rw [this]
      have : (4 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [Real.rpow_add hM0, Real.rpow_one]
    nlinarith

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_windowRank_conditions : SzRow (fun C D L => (nW L C.P.CnW ≤ ((nWv D.R L.sc : ℕ) : ℝ) ∧ ((nWv D.R L.sc : ℕ) : ℝ) < nW L C.P.CnW + 8) ∧ (8 ∣ (nWv D.R L.sc : ℕ)) ∧ (D.R.r + D.R.t = (8 * D.R.f * D.R.r + 4 : ℕ) + (TOv L.sc : ℕ) * (nWv D.R L.sc : ℕ)) ∧ ((TOv L.sc : ℕ) = ⌈L.sc.x ^ C.T.cTO⌉₊) ∧ (Odd (D.R.r + 6 : ℕ)) ∧ (D.R.r + 5 < (D.R.r + 6 : ℕ)) ∧ ((D.R.r + 6 : ℕ) ≤ D.R.r + 7) ∧ (D.R.f * D.R.r * (D.R.r + 1) ≤ (nWv D.R L.sc : ℕ) ∧ (D.R.k - 1) * D.R.f + 2 * D.R.r ≤ (nWv D.R L.sc : ℕ) ∧ (8 * D.R.f * D.R.r + 4 : ℕ) ≤ (nWv D.R L.sc : ℕ))) := by
  first | exact @GlobalTheory.EX.szRow_nW | exact GlobalTheory.EX.szRow_nW | (intros; apply GlobalTheory.EX.szRow_nW <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.explicitChoice_windowRank_le_polyBound : SzRow (fun C D L => ((2 * (D.R.f : ℝ) * D.R.m) ^ 4 * ((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP)) ∧ (((nWv D.R L.sc : ℕ) : ℝ) ≤ (C.T.CP * zBase L ^ C.T.eP))) := by
  first | exact @GlobalTheory.EX.szRow_nW_le_PP | exact GlobalTheory.EX.szRow_nW_le_PP | (intros; apply GlobalTheory.EX.szRow_nW_le_PP <;> assumption)
end
