module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle227
public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.HeckeOne Matrix

noncomputable section

namespace GlobalTheory.OneRep.SplitTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

end GlobalTheory.OneRep.SplitTwist

end
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.InertNbr
open Formalism.L2.DIV (Pl kP St resS oToS idS cmpS)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.InertDivUniq

def minSum (s : List ℕ) (k : ℕ) : ℕ := (s.map (fun a => min a k)).sum

theorem minSum_succ (s : List ℕ) (k : ℕ) :
    minSum s (k + 1) = minSum s k + s.countP (fun a => k < a) := by
  induction s with
  | nil => simp [minSum]
  | cons a s ih =>
    simp only [minSum, List.map_cons, List.sum_cons, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h : k < a
    · simp [h]; omega
    · simp [h]; omega

theorem countP_lt_eq (s : List ℕ) (k : ℕ) :
    s.countP (fun a => k < a) = s.count (k + 1) + s.countP (fun a => k + 1 < a) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.countP_cons, List.count_cons]
    rw [ih]
    by_cases h1 : k < a <;> by_cases h2 : a = k + 1 <;> by_cases h3 : k + 1 < a <;> simp [h1, h2, h3] <;> omega

theorem eq_of_minSum {s t : List ℕ} (hs : s.Pairwise (· ≥ ·)) (hs0 : ∀ a ∈ s, 0 < a)
    (ht : t.Pairwise (· ≥ ·)) (ht0 : ∀ a ∈ t, 0 < a) (h : ∀ k, minSum s k = minSum t k) : s = t := by
  have hc : ∀ k, s.countP (fun a => k < a) = t.countP (fun a => k < a) := fun k => by
    have := minSum_succ s k; have := minSum_succ t k; have := h k; have := h (k + 1); omega
  have hcount : ∀ a, s.count a = t.count a := by
    intro a
    rcases a with _ | a
    · rw [List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (hs0 0 h0)),
        List.count_eq_zero.2 (fun h0 => lt_irrefl 0 (ht0 0 h0))]
    · have := countP_lt_eq s a; have := countP_lt_eq t a; have := hc a; have := hc (a + 1); omega
  exact List.Perm.eq_of_pairwise' hs ht (List.perm_iff_count.2 hcount)

theorem sum_map_eq (s : List ℕ) (f : ℕ → ℕ) : (s.map f).sum = ∑ i : Fin s.length, f (s.get i) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (n := s.length) (fun i => f ((a :: s).get i))).symm

variable {E : Type} [Field E] [NumberField E]

def killedBy {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (I : Ideal (𝓞 E)) : Set M := {x | ∀ r ∈ I, r • x = 0}

theorem card_killedBy_congr {M N : Type} [AddCommGroup M] [Module (𝓞 E) M] [AddCommGroup N] [Module (𝓞 E) N]
    (e : M ≃ₗ[𝓞 E] N) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set M) = Nat.card (killedBy I : Set N) :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    simp only [killedBy, Set.mem_setOf_eq]
    refine forall₂_congr fun r _ => ?_
    rw [LinearEquiv.coe_toEquiv, ← map_smul, LinearEquiv.map_eq_zero_iff])

theorem card_killedBy_inType (Q : Ideal (𝓞 E)) (s : List ℕ) (I : Ideal (𝓞 E)) :
    Nat.card (killedBy I : Set (Formalism.L2.Col.inType Q s)) =
      ∏ i : Fin s.length, Nat.card (killedBy I : Set (𝓞 E ⧸ Q ^ s.get i)) := by
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans Equiv.subtypePiEquivPi)
  simp only [killedBy, Set.mem_setOf_eq]
  constructor
  · intro h i r hr; exact congrFun (h r hr) i
  · intro h r hr; funext i; exact h i r hr

theorem card_quot_pow (Q : Ideal (𝓞 E)) (n : ℕ) : Nat.card (𝓞 E ⧸ Q ^ n) = Ideal.absNorm Q ^ n := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem mem_killedBy_iff (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) (x : 𝓞 E) :
    (∀ r ∈ Q ^ k, r * x ∈ Q ^ a) ↔ x ∈ Q ^ (a - k) := by
  constructor
  · intro H
    rcases le_or_gt a k with hak | hak
    · rw [Nat.sub_eq_zero_of_le hak, pow_zero, Ideal.one_eq_top]; trivial
    · have hle : Q ^ k * Ideal.span {x} ≤ Q ^ a := Ideal.mul_le.2 fun r hr y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        rw [mul_left_comm]; exact Ideal.mul_mem_left _ c (H r hr)
      have hd := Ideal.dvd_iff_le.2 hle
      rw [show Q ^ a = Q ^ k * Q ^ (a - k) by rw [← pow_add]; congr 1; omega] at hd
      have hQ : Q ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
      have := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (pow_ne_zero k hQ)).1 hd)
      exact (Ideal.span_singleton_le_iff_mem _).1 this
  · intro hx r hr
    have := Ideal.mul_mem_mul hr hx
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this

theorem card_killedBy_quot (Q : Ideal (𝓞 E)) (hQ0 : Q ≠ ⊥) (a k : ℕ) :
    Nat.card (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) = Ideal.absNorm Q ^ min a k := by
  have hle : Q ^ a ≤ Q ^ (a - k) := Ideal.pow_le_pow_right (Nat.sub_le a k)
  have hset : (killedBy (Q ^ k) : Set (𝓞 E ⧸ Q ^ a)) =
      (((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)) : Ideal (𝓞 E ⧸ Q ^ a)) : Set (𝓞 E ⧸ Q ^ a)) := by
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [killedBy, Set.mem_setOf_eq, SetLike.mem_coe, Ideal.mem_quotient_iff_mem hle]
    rw [← mem_killedBy_iff Q hQ0 a k x]
    refine forall₂_congr fun r _ => ?_
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rw [hset]
  have h1 := Submodule.card_eq_card_quotient_mul_card ((Q ^ (a - k)).map (Ideal.Quotient.mk (Q ^ a)))
  rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv, card_quot_pow, card_quot_pow] at h1
  have hq : 0 < Ideal.absNorm Q := Nat.pos_of_ne_zero (fun h0 => hQ0 (Ideal.absNorm_eq_zero_iff.1 h0))
  have ha : Ideal.absNorm Q ^ a = Ideal.absNorm Q ^ min a k * Ideal.absNorm Q ^ (a - k) := by
    rw [← pow_add]; congr 1; omega
  rw [ha] at h1
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos hq _) h1).symm

theorem inType_exps_unique : ∀ {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (s t : List ℕ),
    s.Pairwise (· ≥ ·) → (∀ a ∈ s, 0 < a) → t.Pairwise (· ≥ ·) → (∀ a ∈ t, 0 < a) →
    Nonempty (inType Q.asIdeal s ≃ₗ[𝓞 E] inType Q.asIdeal t) → s = t := by
  intro E _ _ Q s t hs hs0 ht ht0 ⟨e⟩
  refine eq_of_minSum hs hs0 ht ht0 fun k => ?_
  have hq : 2 ≤ Ideal.absNorm Q.asIdeal := by
    have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h1 => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)
    omega
  have key : ∀ u : List ℕ, Nat.card (killedBy (Q.asIdeal ^ k) : Set (inType Q.asIdeal u)) =
      Ideal.absNorm Q.asIdeal ^ minSum u k := fun u => by
    rw [card_killedBy_inType, minSum, sum_map_eq, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => card_killedBy_quot Q.asIdeal Q.ne_bot _ k
  have := card_killedBy_congr e (Q.asIdeal ^ k)
  rw [key, key] at this
  exact Nat.pow_right_injective hq this

end GlobalTheory.InertDivUniq
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVectors_injective_nonzero_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → IsThetaFunO ψ S T f → f ≠ 0 → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → Function.Injective (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f) := by
  first | exact @GlobalTheory.FockIndep.pureTensorO_injective | exact GlobalTheory.FockIndep.pureTensorO_injective | (intros; apply GlobalTheory.FockIndep.pureTensorO_injective <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices



theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T0), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (M' : IntermediateField ℚ ℂ), M ≤ M' → ∀ bad : ℕ, D.host.g 0 * D.host.g 1 ∣ bad → (∀ PP ∈ R.Q t, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∃ B : Ideal (𝓞 D.host.E) → M', BIs R i M'.val.toRingHom t bad B := by
  first | exact @GlobalTheory.Mem.BVal.exists_field_BIs | exact GlobalTheory.Mem.BVal.exists_field_BIs | (intros; apply GlobalTheory.Mem.BVal.exists_field_BIs <;> assumption)
end

section

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapTuples

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def XiConst (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (c0 : ℂ) : Prop :=
  ∀ t, GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC O.c') (O.dδ t) (O.U₂ t) (O.dict₂ t) ι x₀ (O.xi t) c0

abbrev IsCls (t : Tp) (x : O.Cl' t → VsV D i O.c'.F) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev rdQ (z : G) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : AutQ (Wc D i) → ℂ :=
  jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu (actLev O.c' O.lev2 z f)

def ClsEx : Prop :=
  ∀ t x, O.Plc t x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank, IsCls O t x f ∧
      ∀ f' ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f' → f' = f

def PtIdent (lam : AutQ (Wc D i) → ℂ) (z : G) (c0 : ℂ) : Prop :=
  ∀ t, ∃ ze : ℂ, ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x, O.Plc t x →
    ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f →
      ∀ q, c0 * O.thAd t x q = ze * lam q * rdQ O z f q

end Data

abbrev liftQ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) (t : T0) (x : A.fam.amb.FL i t) : AutQ (Wc D i) → ℂ :=
  onQ (Wc D i) (R.thF i t (jVx R i t x) v)

def LiftsSpan {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∀ (t : T0) (x : A.fam.amb.FL i t), liftQ R i v t x ∈ Submodule.span ℂ (Set.range (liftQ R i v A.μ0))

def PinsExist (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

end GlobalTheory.OneMapTuples
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

theorem _root_.GlobalTheory.T.exists_unramified_cmType_heckeChar_on_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ χ : _root_.Formalism.L2.Host.HChar H.E, _root_.Formalism.L2.Host.IsChiPsi H χ := by
  first | exact @GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | exact GlobalTheory.Mem.ChiPsiExist.exists_chiPsi | (intros; apply GlobalTheory.Mem.ChiPsiExist.exists_chiPsi <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
end
