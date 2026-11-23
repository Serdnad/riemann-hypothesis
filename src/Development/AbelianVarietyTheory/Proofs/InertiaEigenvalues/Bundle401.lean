module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle381
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle001
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle090
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle006
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.exists_dualLattice_isOpen_perfectPairing : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  first | exact @GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | exact GlobalTheory.Pass.LocDual.exists_dualLat_isOpen | (intros; apply GlobalTheory.Pass.LocDual.exists_dualLat_isOpen <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.ThetaTie
open _root_.Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow {P : LocPrime l} (AI : LocAinf l P) (m n : ℕ) : AI.ζ (m + n) ^ l ^ n = AI.ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem isEps {P : LocPrime l} (AI : LocAinf l P) : IsEps (l := l) AI.ε := by
  constructor
  · refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
    have := zeta_pow AI 0 n
    rw [zero_add, AI.ζ_zero] at this
    rw [this]
  · have : ((frobeniusEquiv (Per.Fl l) l).symm AI.ε).untilt = AI.ζ 1 := by
      refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
      refine ⟨AI.ζ (1 + n), ?_, ?_⟩
      · rw [add_comm]
        exact (AI.ε_coeff (n + 1)).symm.trans (PreTilt.coeff_frobeniusEquiv_symm n _).symm
      · rw [zeta_pow AI 1 n]
    rw [this]
    exact AI.ζ_one

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  have : Subsingleton (Per.AinfP l ⧸ Per.kerP l ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]; infer_instance
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 0 y).2 (Subsingleton.elim _ _)

theorem mem_filD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact GlobalTheory.RingIface.exists_of_mem_FilD_nat l
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem alg_inj {e : Per.Fl l} (he : IsEps e) :
    Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := by
  have _ := he
  exact (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem log_mu {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have hm : algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
    refine GlobalTheory.RingIface.alg_mem_kerP l ?_
    rw [map_sub, WittVector.fontaineTheta_teichmuller, he.1, map_one, sub_self]
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  change Per.ev l 2 (algebraMap (Per.AinfP l) (Per.BdRp l)
    (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) - y) = 0
  rw [map_sub, ev_alg]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = m at hm h ⊢
  have h2 : Ideal.Quotient.mk (Per.kerP l ^ 2) (m ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hm 2)
  have hu : IsUnit ((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  have hs : (∑ k ∈ Finset.range 2, (-1) ^ k * (((2 : ℕ).factorial / (k + 1) : ℕ) : Per.AinfP l) *
      m ^ (k + 1)) = ((2 : ℕ) : Per.AinfP l) * m - m ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hs, map_sub, h2, sub_zero, map_mul, map_natCast] at h
  rw [sub_eq_zero]
  exact (hu.mul_left_cancel h).symm

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem eD_ιA (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  refine Eq.trans ?_ h
  simp

theorem fil_nat (n : ℕ) (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil n ↔
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (T.fil _ _ _).trans (mem_filD_nat n _)

theorem fil_zero (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil 0 ↔
    ∃ z, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (fil_nat T 0 x).trans ⟨fun ⟨z, _, h⟩ => ⟨z, h⟩, fun ⟨z, h⟩ => ⟨z, mem_filtration_zero' z, h⟩⟩

def th (x : P.R.BdR) : ℂ_[l] :=
  Per.θD l (Function.invFun (algebraMap (Per.BdRp l) (Per.BdR l)) (T.eD x))

theorem th_eq {x : P.R.BdR} {z : Per.BdRp l}
    (h : algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x) : th T x = Per.θD l z := by
  rw [th, ← h, Function.leftInverse_invFun (alg_inj (isEps AI))]

include T in
theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD (botExt l)).Fil (-1), P.ιB P.tB * s = 1 := by
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l _ (isEps AI)
  obtain ⟨-, hk, hun, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hu := (P.PD (botExt l)).t_unit
  have t1 := (P.PD (botExt l)).mem_filtration_one
  have t2 := (P.PD (botExt l)).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at t1 t2
  rw [P.period_datum_t_eq] at hu
  obtain ⟨s, hs⟩ := (hu.map P.ιB).exists_right_inv
  refine ⟨s, ?_, hs⟩
  obtain ⟨z, hz, ez⟩ := (fil_nat T 1 _).1 t1
  obtain ⟨u, rfl⟩ := (h1 1 z).1 hz
  have huu : IsUnit u := hun u fun h0 => by
    obtain ⟨w, rfl⟩ := (h1 1 u).1 ((hk u).1 h0)
    exact t2 ((fil_nat T 2 _).2 ⟨_, (h1 2 _).2 ⟨w, by ring⟩, ez⟩)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  rw [T.fil, GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l _ (isEps AI)]
  refine ⟨v, ?_⟩
  have e1 : T.eD (P.ιB P.tB) * T.eD s = 1 := by rw [← map_mul, hs, map_one]
  have e2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv
  rw [← ez] at e1
  rw [show (- (-1 : ℤ)).toNat = 1 from rfl, show (-1 : ℤ).toNat = 0 from rfl]
  simp only [map_mul, map_one, pow_one, pow_zero, one_mul] at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi AI.ε)) = X at e1 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) u = U at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) v = V at e2 ⊢
  linear_combination V * e1 - (T.eD s * X) * e2

def thetaL : ThetaL P AI where
  θ := th T
  θ_one := by rw [th_eq T (z := 1) (by simp), map_one]
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a + b) (by rw [map_add (f := _), map_add (f := _), ha, hb]), map_add (f := _)]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨z, hz⟩ := (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).1 c
    have e : algebraMap (Per.BdRp l) (Per.BdR l) z =
        T.eD (T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) z)) := (T.eD.apply_symm_apply _).symm
    exact ⟨_, (fil_zero T _).2 ⟨z, e⟩, (th_eq T e).trans hz⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    rw [th_eq T ha, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1]
    refine ⟨fun h => (fil_nat T 1 x).2 ⟨a, h, ha⟩, fun h => ?_⟩
    obtain ⟨z, hz, e⟩ := (fil_nat T 1 x).1 h
    rwa [← alg_inj (isEps AI) (e.trans ha.symm)]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g a) = T.eD (P.actQdR g x) := by
      rw [T.actD, ← ha]
      exact (GlobalTheory.RingIface.sigD_alg l g a).symm
    rw [th_eq T ha, th_eq T e, actC_eq, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2]
  θ_Om x := by
    obtain ⟨y, h1, h2⟩ := T.om x
    rw [th_eq T h1.symm, h2]
  θ_int a := by
    rw [th_eq T (eD_ιA T a).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  θ_teich x y h := by
    rw [th_eq T (eD_ιA T _).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, WittVector.fontaineTheta_teichmuller]
    have h1 := Ideal.Quotient.eq.1 ((PreTilt.mk_untilt_eq_coeff_zero x).trans h)
    have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
    simpa using h2
  fil_succ_iff_mul_t a x := by
    have t1 := (P.PD (botExt l)).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at t1
    constructor
    · intro hx
      obtain ⟨s, hs, e⟩ := exists_inverse_fontaineElement_mem_fil_neg_one T
      refine ⟨s * x, ?_, by rw [← mul_assoc, e, one_mul]⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ hs hx
      rwa [show -1 + (a + 1) = a by ring] at this
    · rintro ⟨y, hy, rfl⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ t1 hy
      rwa [add_comm] at this
  t_μ := by
    obtain ⟨y, hy, e⟩ := T.t
    refine (fil_nat T 2 _).2 ⟨_, log_mu (isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, eD_ιA]
    rfl

theorem nonempty_thetaL (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] :
    Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  ⟨thetaL (D.locT l)⟩

end GlobalTheory.ThetaTie
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem cLL_unit_interval_le : ∀ (l h N v : ℕ) (U : Finset ℤ) (U' : Set ℤ), l.Prime → 1 ≤ N → U' ⊆ U → U.card ≤ N →
    (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) → v ≤ LocalSituation.mN l 1 (h + h) - 1 →
    LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v U' 0 1 ≤ 5 + Nat.log l (2 * h) + N * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  intro l h N v U U' hl hN hU hcard hb hv
  haveI : Fact l.Prime := ⟨hl⟩
  unfold LocalSituation.cLL LocalSituation.mN LocalSituation.rI LocalSituation.n0 at *
  set L := Nat.log l (2 * h) with hL
  set n0 := sInf {n | h + h ≤ l ^ n * (l - 1)} with hn0
  have hl1 : 1 < l := hl.one_lt

  have hn0le : n0 ≤ L + 1 := by
    apply Nat.sInf_le
    show h + h ≤ l ^ (L + 1) * (l - 1)
    have h1 : 2 * h < l ^ (L + 1) := Nat.lt_pow_succ_log_self hl1 (2 * h)
    have h2 : l ^ (L + 1) ≤ l ^ (L + 1) * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton]

  have hterm : ∀ u ∈ U,
      (∑ᶠ (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ 4 + 2 * L := by
    intro u hu
    have hz : LocalSituation.vZ l u ≤ Nat.log l h := vZ_le_log l h u (hb u hu)
    have hlog : Nat.log l h ≤ L := Nat.log_mono_right (by omega)
    simp only [finsum_eq_if, sub_zero]
    split_ifs <;> omega

  have hS : (∑ᶠ (u : ℤ) (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0)))
      ≤ N * (4 + 2 * L) := by
    rw [finsum_eq_sum_of_support_subset _ (s := U) ?_]
    · calc _ ≤ U.card • (4 + 2 * L) := Finset.sum_le_card_nsmul _ _ _ hterm
        _ ≤ N * (4 + 2 * L) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
    · intro u hu
      rw [Function.mem_support] at hu
      by_contra hnot
      have hnU' : u ∉ U' := fun h' => hnot (Finset.mem_coe.mpr (hU h'))
      exact hu (by simp only [finsum_eq_if, if_neg hnU'])
  have hNL : 1 ≤ N * (4 + 2 * L) := by
    have := Nat.mul_le_mul hN (show 1 ≤ 4 + 2 * L by omega)
    omega
  have hmax := max_le hNL hS
  omega

end GlobalTheory.HubLoc
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.IntegralModelOverCoeff

open scoped Matrix

theorem exists_integral_conj {l : ℕ} [Fact l.Prime] {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (a : ℕ) (ρ : Γ →* GL (Fin a) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hK : ∀ g s t, ∃ x, ι x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t) :
    ∃ (r : Γ →* GL (Fin a) O) (Pm : GL (Fin a) (Qbar l)),
      ∀ g, mapRep (ι.comp (algebraMap O (FractionRing O))) r g = Pm⁻¹ * ρ g * Pm := by
  classical
  set K := FractionRing O
  choose f hf using hK
  have hιi : Function.Injective (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro A B h
    ext s t
    exact ι.injective (congrFun (congrFun h s) t)
  have hM : ∀ g, ι.mapMatrix (Matrix.of (f g)) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; ext s t; exact hf g s t
  let ρ0 : Γ →* Matrix (Fin a) (Fin a) K :=
    { toFun := fun g => Matrix.of (f g)
      map_one' := hιi (by rw [hM, map_one, map_one, Units.val_one])
      map_mul' := fun g h => hιi (by rw [map_mul, hM, hM, hM, map_mul, Units.val_mul]) }
  let ρK : Γ →* GL (Fin a) K := ρ0.toHomUnits
  have hρK : ∀ g, ι.mapMatrix ((ρK g : GL _ _) : Matrix (Fin a) (Fin a) K) =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := fun g => hM g

  let Int : Set (Matrix (Fin a) (Fin a) (Qbar l)) := {M | ∀ s t, ‖M s t‖ ≤ 1}
  have hInt1 : (1 : Matrix (Fin a) (Fin a) (Qbar l)) ∈ Int := by
    intro s t
    by_cases h : s = t
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hIntMul : ∀ A B, A ∈ Int → B ∈ Int → A * B ∈ Int := by
    intro A B hA hB s t
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA s k) (norm_nonneg _) (hB k t)
  have hIntOpen : IsOpen Int := by
    have : Int = ⋂ s, ⋂ t, (fun M : Matrix (Fin a) (Fin a) (Qbar l) => M s t) ⁻¹' Metric.closedBall 0 1 := by
      ext M; simp [Int]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage (continuous_id.matrix_elem s t)
  let U : Subgroup Γ :=
    { carrier := {g | ((ρ g : GL _ _) : Matrix _ _ _) ∈ Int ∧ ((ρ g⁻¹ : GL _ _) : Matrix _ _ _) ∈ Int}
      one_mem' := by simp [hInt1]
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul]; exact hIntMul _ _ hg1 hh1
        · rw [mul_inv_rev, map_mul, Units.val_mul]; exact hIntMul _ _ hh2 hg2
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        exact ⟨h2, by rwa [inv_inv]⟩ }
  have hUopen : IsOpen (U : Set Γ) :=
    (hIntOpen.preimage hc).inter (hIntOpen.preimage (hc.comp continuous_inv))
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUint : ∀ h ∈ U, ∀ i j, ((ρK h : GL _ _) : Matrix (Fin a) (Fin a) K) i j ∈ (algebraMap O K).range := by
    intro h hh i j
    rw [GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι]
    have := congrFun (congrFun (hρK h) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    exact hh.1 i j
  obtain ⟨P, hP⟩ := GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.exists_conj_integral (O := O) a ρK U hUint
  choose e he using hP
  have hai : Function.Injective ((algebraMap O K).mapMatrix :
      Matrix (Fin a) (Fin a) O →+* Matrix (Fin a) (Fin a) K) := by
    intro A B h
    ext s t
    exact IsFractionRing.injective O K (congrFun (congrFun h s) t)
  have hE : ∀ g, (algebraMap O K).mapMatrix (Matrix.of (e g)) =
      ((P * ρK g * P⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
    intro g; ext s t; exact he g s t
  let r0 : Γ →* Matrix (Fin a) (Fin a) O :=
    { toFun := fun g => Matrix.of (e g)
      map_one' := hai (by rw [hE, map_one, map_one, mul_one, mul_inv_cancel, Units.val_one])
      map_mul' := fun g h => hai (by
        rw [map_mul, hE, hE, hE, ← Units.val_mul, map_mul]
        congr 1
        group) }
  refine ⟨r0.toHomUnits, (Units.map (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* _).toMonoidHom P)⁻¹, fun g => ?_⟩
  ext1
  rw [inv_inv]
  show (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) = _
  have : (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) =
      ι.mapMatrix ((algebraMap O K).mapMatrix (Matrix.of (e g))) := by
    ext s t; rfl
  rw [this, hE, Units.val_mul, Units.val_mul, map_mul, map_mul, hρK]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.IntegralModelOverCoeff

namespace GlobalTheory.IntegralModelOverCoeff

open Formalism.MainNotions.SumRepresentations

theorem exists_integral_model_rep : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ hc hK
  exact exists_integral_conj (A.iotaQ i) (A.iotaQ_alg i) a ρ hc hK

end GlobalTheory.IntegralModelOverCoeff
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented : ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ), 0 < m → ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B), (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧ x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  first | exact @GlobalTheory.SqZeroPow.exists_ring | exact GlobalTheory.SqZeroPow.exists_ring | (intros; apply GlobalTheory.SqZeroPow.exists_ring <;> assumption)
end
