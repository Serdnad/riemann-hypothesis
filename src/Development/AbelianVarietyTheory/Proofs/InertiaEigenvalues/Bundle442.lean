module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOrderAboveLFiniteModules
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle887
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle425
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Mathlib.RingTheory.Nilpotent.Exp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle269
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle401
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle427
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle429
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.localConditionOrder_aboveL_finiteModules : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → LocSat bkP i s κ → LocCount bkP i s κ → LocCountFin bkP i s κ := by
  first | exact @GlobalTheory.LocCountFinite.locCountFin | exact GlobalTheory.LocCountFinite.locCountFin | (intros; apply GlobalTheory.LocCountFinite.locCountFin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  first | exact @GlobalTheory.StageFirst.firstHalf | exact GlobalTheory.StageFirst.firstHalf | (intros; apply GlobalTheory.StageFirst.firstHalf <;> assumption)
end

section

noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := GlobalTheory.T.jacobi_trudi_alternant_expansion (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP

  simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleRing_image_add_ell_pi_adic_closed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (x : RW LL), (∀ m, ∃ e, NearPi AI LL s m (x - E.tie.ioE e)) → ∃ e r, x - E.tie.ioE e = (l : RW LL) * r := by
  first | exact @GlobalTheory.Decompl.ioE_closed | exact GlobalTheory.Decompl.ioE_closed | (intros; apply GlobalTheory.Decompl.ioE_closed <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleRing_image_saturated_adicClosed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (x : RW LL) (e : W.EE), (l : RW LL) * x = E.tie.ioE e → ∃ e', x = E.tie.ioE e') ∧ ∀ x : RW LL, (∀ k : ℕ, ∃ e r, x - E.tie.ioE e = (l : RW LL) ^ k * r) → ∃ e, x = E.tie.ioE e := by
  first | exact @GlobalTheory.Decompl.Sat.ioE_saturated_closed | exact GlobalTheory.Decompl.Sat.ioE_saturated_closed | (intros; apply GlobalTheory.Decompl.Sat.ioE_saturated_closed <;> assumption)
end

section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.MirTower
open scoped ENNReal

theorem _root_.GlobalTheory.T.lintegral_theta_series_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.lintegral_theta_unfold | exact GlobalTheory.ThetaUnfold.lintegral_theta_unfold | (intros; apply GlobalTheory.ThetaUnfold.lintegral_theta_unfold <;> assumption)
end

section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
end

section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem eq_of_pow_eq_of_nilpotent {Q : Type*} [CommRing Q] {a b : Q} {N : ℕ} (hN : IsUnit (N : Q))
    (hb : IsUnit b) (hn : IsNilpotent (a - b)) (h : a ^ N = b ^ N) : a = b := by
  have h1 := (Commute.all a b).geom_sum₂_mul N
  rw [h, sub_self] at h1
  have h2 : IsNilpotent ((∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) - N * b ^ (N - 1)) := by
    have e : (N : Q) * b ^ (N - 1) = ∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i) := by
      rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [e, ← Finset.sum_sub_distrib, ← mem_nilradical]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b i
    rw [hc, mul_assoc]
    exact Ideal.mul_mem_right _ _ (mem_nilradical.2 hn)
  have h3 := h2.isUnit_add_right_of_commute (hN.mul (hb.pow (N - 1))) (Commute.all _ _)
  rw [sub_add_cancel] at h3
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h1)

theorem nilpotent_exp_nsmul {Q : Type*} [CommRing Q] [Module ℚ Q] {x : Q} (hx : IsNilpotent x) (n : ℕ) :
    IsNilpotent.exp ((n : Q) * x) = IsNilpotent.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      ((Commute.all _ _).isNilpotent_mul_left hx) hx, ih, pow_succ]

theorem pow_eq_mul_exp {K Q : Type*} [Field K] [CharZero K] [CommRing Q] [Algebra K Q] {a z t : Q}
    {M N : ℕ} (m : ℕ) (hN : N ≠ 0) (ht : t ^ M = 0) (hz : z ^ N = 1) (hn : IsNilpotent (a - z))
    (ha : a ^ N = ∑ j ∈ Finset.range M, algebraMap K Q ((j.factorial : K)⁻¹) * t ^ j) :
    a ^ m = z ^ m * ∑ j ∈ Finset.range M,
      algebraMap K Q (((m : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
  letI : Algebra ℚ Q := ((algebraMap K Q).comp (algebraMap ℚ K)).toAlgebra
  have hE : ∀ c : K, IsNilpotent.exp (algebraMap K Q c * t) =
      ∑ j ∈ Finset.range M, algebraMap K Q (c ^ j / (j.factorial : K)) * t ^ j := by
    intro c
    rw [IsNilpotent.exp_eq_sum (k := M) (by rw [mul_pow, ht, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_pow, ← mul_assoc, ← map_pow, div_eq_inv_mul, map_mul]
    congr 2
    change algebraMap K Q (algebraMap ℚ K _) = _
    simp
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : IsNilpotent (algebraMap K Q (N : K)⁻¹ * t) :=
    (Commute.all _ _).isNilpotent_mul_left ⟨M, ht⟩
  have hk : ∀ k : ℕ, IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) ^ k =
      ∑ j ∈ Finset.range M, algebraMap K Q (((k : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
    intro k
    rw [← nilpotent_exp_nsmul hx, ← hE, div_eq_mul_inv, map_mul, map_natCast, mul_assoc]
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz hN
  have e : a = z * IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) := by
    refine eq_of_pow_eq_of_nilpotent (N := N) ?_ (hu.mul hx.isUnit_exp) ?_ ?_
    · have := (IsUnit.mk0 _ hN').map (algebraMap K Q)
      rwa [map_natCast] at this
    · have h1 := (Commute.all z _).isNilpotent_mul_left hx.isNilpotent_exp_sub_one
      have h2 := (Commute.all _ _).isNilpotent_sub hn h1
      convert h2 using 1
      ring
    · rw [mul_pow, hz, one_mul, hk, ha]
      simp [div_self hN']
  rw [e, mul_pow, hk]

variable {l : ℕ} [Fact l.Prime]

def filZero (P : LocPrime l) : Subalgebra ℚ_[l] P.R.BdR where
  carrier := {x | x ∈ FilB P 0}
  mul_mem' hx hy := FilB_zero_mul hx hy
  add_mem' hx hy := (FilB P 0).add_mem hx hy
  algebraMap_mem' c := qB_mem c

def filIdeal (P : LocPrime l) (M : ℕ) : Ideal ↥(filZero P) where
  carrier := {x | (x : P.R.BdR) ∈ FilB P (M : ℤ)}
  zero_mem' := (FilB P (M : ℤ)).zero_mem
  add_mem' hx hy := (FilB P (M : ℤ)).add_mem hx hy
  smul_mem' c _ hx := FilB_zero_mul c.2 hx

theorem epsT_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ l ^ s = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow]
  congr 1
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    rfl

theorem ζQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ l ^ s = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ n ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem oB_mem_zero {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) :
    oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem epsT_sub_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (s : ℕ) :
    io AI (epsT AI s) - oB P (P.ζQ s) ∈ FilB P 1 := by
  obtain ⟨y, h1, h2⟩ := T.om (P.ζQ s)
  refine (GlobalTheory.ThetaTie.fil_nat T 1 _).2 ⟨GlobalTheory.MemLoc.aDp l (epsT AI s) - y, ?_, ?_⟩
  · rw [← (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1, map_sub, h2, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, epsT,
      WittVector.fontaineTheta_teichmuller, untilt_εroot, AI.ζ_eq, sub_self]
  · rw [map_sub, map_sub, h1, io_apply, GlobalTheory.ThetaTie.eD_ιA]

theorem epsT_pow_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) *
      ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) *
        tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI T s m M
  let π := Ideal.Quotient.mkₐ ℚ_[l] (filIdeal P M)
  have hπ : ∀ x y : ↥(filZero P), π x = π y ↔ (x : P.R.BdR) - y ∈ FilB P (M : ℤ) :=
    fun x y => Ideal.Quotient.eq
  have hnil : ∀ x : ↥(filZero P), (x : P.R.BdR) ∈ FilB P 1 → π x ^ M = 0 := by
    intro x hx
    rw [← map_pow, ← map_zero π, hπ]
    simpa using FilB_pow hx M
  let a : ↥(filZero P) := ⟨io AI (epsT AI s), io_mem AI _⟩
  let z : ↥(filZero P) := ⟨oB P (P.ζQ s), oB_mem_zero T _⟩
  let t : ↥(filZero P) := ⟨tD P, FilB_anti zero_le_one tD_mem⟩
  have hs : ∀ c : ℕ → ℚ_[l], ∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * π t ^ j =
      π (∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j) := by
    intro c

    simp only [map_sum, map_mul, map_pow, AlgHom.commutes]
  have hc : ∀ c : ℕ → ℚ_[l],
      ((∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j : ↥(filZero P)) : P.R.BdR) =
      ∑ j ∈ Finset.range M, qB P (c j) * tD P ^ j := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl
  have key := pow_eq_mul_exp (K := ℚ_[l]) (a := π a) (z := π z) (t := π t) (M := M) (N := l ^ s) m
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (hnil t tD_mem)
    (by
      rw [← map_pow, ← map_one π]
      congr 1
      apply Subtype.ext
      change oB P (P.ζQ s) ^ l ^ s = 1
      rw [← map_pow, ζQ_pow, map_one])
    ⟨M, by rw [← map_sub]; exact hnil _ (epsT_sub_mem T s)⟩
    (by
      rw [hs (fun j => (j.factorial : ℚ_[l])⁻¹), ← map_pow, hπ, hc]
      change io AI (epsT AI s) ^ l ^ s - _ ∈ _
      rw [← map_pow, epsT_pow]
      exact GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration l P AI T M)
  rw [hs (fun j => ((m : ℚ_[l]) / ((l ^ s : ℕ) : ℚ_[l])) ^ j / (j.factorial : ℚ_[l])), ← map_pow,
    ← map_pow, ← map_mul, hπ, Subalgebra.coe_mul, hc, Nat.cast_pow] at key
  rw [map_pow, map_pow]
  exact key

end GlobalTheory.ExpImage
end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_global_approx_of_artin_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ), art (Neutral.B1.localIdele E w x) = 1 →
    (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - (x : w.adicCompletion E)) ≤ Valued.v t) := by
  first | exact @GlobalTheory.ArtinApprox.exists_global_approx | exact GlobalTheory.ArtinApprox.exists_global_approx | (intros; apply GlobalTheory.ArtinApprox.exists_global_approx <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem _root_.GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : _root_.Formalism.ConjugateSelfDual.G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  first | exact @GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq | exact GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq | (intros; apply GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.epsilon_unique_of_inductive : BrauerDegreeZero → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ε ε' : WD h → ℂˣ), (∀ x y, ε (x.lpSum y) = ε x * ε y) → (∀ x y, ε' (x.lpSum y) = ε' x * ε' y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → ε x = ε y ∧ ε' x = ε' y) → (∀ ξ hξ, ε (WD.lpOfChar h ξ hξ) = ε' (WD.lpOfChar h ξ hξ)) → (∀ (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∀ (χ₁ χ₂ : H →* ℂˣ) (n : ℕ) (b₁ b₂ : WDRep h (Fin n → ℂ)) (v₁ v₂ : Fin n → ℂ), n = H.index → (∀ σ : H, b₁.ρ σ v₁ = (χ₁ σ : ℂ) • v₁) → (∀ σ : H, b₂.ρ σ v₂ = (χ₂ σ : ℂ) • v₂) → Submodule.span ℂ (Set.range fun σ => b₁.ρ σ v₁) = ⊤ → Submodule.span ℂ (Set.range fun σ => b₂.ρ σ v₂) = ⊤ → ε (WD.mk b₁) * ε' (WD.mk b₂) = ε (WD.mk b₂) * ε' (WD.mk b₁)) → ∀ x, ε x = ε' x := by
  first | exact @GlobalTheory.WeilBrauer.eq_of_induced | exact GlobalTheory.WeilBrauer.eq_of_induced | (intros; apply GlobalTheory.WeilBrauer.eq_of_induced <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eq_one_of_approx_by_congruent_global_units : ChevalleyUnits → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E), Valued.v x = 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → x = 1 := by
  first | exact @GlobalTheory.eq_one_of_approx_by_congruent_units | exact GlobalTheory.eq_one_of_approx_by_congruent_units | (intros; apply GlobalTheory.eq_one_of_approx_by_congruent_units <;> assumption)
end
