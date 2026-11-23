module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJump
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.LemZ

theorem weier : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := GlobalTheory.T.weierstrass_preparation_wittOfTiltFiniteField

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P Q : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → frobS l a (P : (Wq l a)⟦X⟧) ∣ (Q : (Wq l a)⟦X⟧) →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ Q := GlobalTheory.T.expand_map_dvd_of_breuilKisinFrobenius_dvd

theorem coeffZero : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := GlobalTheory.T.coeff_zero_ne_zero_of_wittFrobenius_expand_dvd

theorem frobAut : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a], ∃ Φ : Om l ≃ₐ[ℚ_[l]] Om l,
    ∀ w : Wq l a, Φ (GlobalTheory.TameFrob.iotaO l a w) = GlobalTheory.TameFrob.iotaO l a (sigma l a w) := GlobalTheory.T.exists_algEquiv_extending_wittTiltFrobenius

theorem rootLt : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := GlobalTheory.T.norm_lt_one_of_isRoot_distinguished_witt_polynomial

theorem irr : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic → 0 < E.natDegree →
    (∀ i < E.natDegree, (l : Wq l a) ∣ E.coeff i) → (∃ w : (Wq l a)ˣ, E.coeff 0 = (l : Wq l a) * w) →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) := GlobalTheory.T.irreducible_map_unramifiedWittToFractionField_of_eisenstein

theorem conj : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (z z' : Om l),
    Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ‖z'‖ = ‖z‖ := GlobalTheory.T.norm_eq_of_isRoot_minpoly_unramifiedRootsOfUnityField

theorem expandCoeff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (E : Polynomial (Wq l a)), E.Monic →
    Irreducible (E.map (GlobalTheory.TameFrob.iota l a)) → ∀ z : Om l, z ≠ 0 →
    (∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (E.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot y) →
    ∀ i, ¬ l ∣ i → E.coeff i = 0 := GlobalTheory.T.coeff_eq_zero_of_roots_contain_lth_roots_conjugates

theorem isUnit_of_frob_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ g : bk.S, ¬ (l : bk.S) ∣ g →
    ∀ M : ℕ, frobS l bk.a g ∣ bk.E ^ M * g → IsUnit g := by
  intro l _ K bk g hg M hdvd
  classical
  obtain ⟨P, U, hU, hPm, hPd, rfl⟩ := weier l bk.a g hg
  have h1 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ ((bk.Ep ^ M * P : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) := by
    rw [map_mul] at hdvd
    have h3 : frobS l bk.a (P : (Wq l bk.a)⟦X⟧) ∣ bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U := by
      have := (dvd_mul_left _ _).trans hdvd
      rw [show bk.E ^ M * (U * (P : (Wq l bk.a)⟦X⟧)) = bk.E ^ M * (P : (Wq l bk.a)⟦X⟧) * U by ring] at this
      exact this
    rw [Polynomial.coe_mul, Polynomial.coe_pow]
    exact hU.dvd_mul_right.1 h3
  have h2 := descend l bk.a P _ hPm hPd h1
  by_cases hd : P.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hPm hd, Polynomial.coe_one, mul_one]
    exact hU
  exfalso
  have hl0 : (l : Wq l bk.a) ≠ 0 := fun h => by
    have := congrArg (GlobalTheory.TameFrob.iotaO l bk.a) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)
  have hE0 : bk.Ep.coeff 0 ≠ 0 := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    rw [hw]
    exact mul_ne_zero hl0 w.ne_zero
  have hP0 := coeffZero l bk.a P bk.Ep M hPm hE0 h2
  set ι := GlobalTheory.TameFrob.iotaO l bk.a with hι
  have hιinj : Function.Injective ι := GlobalTheory.TameFrob.iotaO_injective l bk.a
  set Pι := P.map ι with hPι
  have hPι0 : Pι ≠ 0 := (hPm.map ι).ne_zero
  have hdeg : Pι.degree ≠ 0 := by
    rw [hPι, Polynomial.degree_map_eq_of_injective hιinj, Polynomial.degree_eq_natDegree hPm.ne_zero]
    exact_mod_cast hd
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_root Pι hdeg
  have hne : Pι.roots.toFinset.Nonempty := ⟨x0, Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hx0)⟩
  obtain ⟨x, hxs, hxmax⟩ := Finset.exists_max_image _ (fun y : Om l => ‖y‖) hne
  have hx : Pι.IsRoot x := (Polynomial.mem_roots hPι0).1 (Multiset.mem_toFinset.1 hxs)
  have hmax : ∀ y : Om l, Pι.IsRoot y → ‖y‖ ≤ ‖x‖ := fun y hy =>
    hxmax y (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hPι0).2 hy))
  set r := ‖x‖ with hr
  have hr1 : r < 1 := rootLt l bk.a P hPm hPd x hx
  have hxne : x ≠ 0 := by
    rintro rfl
    apply hP0
    apply hιinj
    simpa [hPι, Polynomial.IsRoot, Polynomial.eval_zero_map, ← Polynomial.coeff_zero_eq_eval_zero] using hx
  have hr0 : 0 < r := norm_pos_iff.2 hxne
  obtain ⟨Φ, hΦ⟩ := frobAut l bk.a
  have hn : ∀ y, ‖Φ y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv Φ y).symm
  set z := Φ x with hzdef
  have hz : ‖z‖ = r := hn x
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; exact hr0.ne hz
  set Q := P.map (sigma l bk.a : Wq l bk.a →+* Wq l bk.a) with hQ
  have hQι : Q.map ι = Pι.map (Φ : Om l →+* Om l) := by
    rw [hQ, hPι, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext w
    exact (hΦ w).symm
  have hzQ : (Q.map ι).IsRoot z := by
    rw [hQι]
    exact hx.map (Φ : Om l →+* Om l)
  have hcomp : (algebraMap (↥(Kunr l bk.a)) (Om l)).comp (GlobalTheory.TameFrob.iota l bk.a) = ι := RingHom.ext fun w => rfl
  have haev : ∀ y : Om l, Polynomial.aeval y (Q.map (GlobalTheory.TameFrob.iota l bk.a)) = (Q.map ι).eval y := fun y => by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, Polynomial.eval_map]
  have hmdvd : minpoly (↥(Kunr l bk.a)) z ∣ Q.map (GlobalTheory.TameFrob.iota l bk.a) := by
    apply minpoly.dvd
    rw [haev]
    exact hzQ
  have key : ∀ z' : Om l, Polynomial.aeval z' (minpoly (↥(Kunr l bk.a)) z) = 0 → ∀ y : Om l, y ^ l = z' →
      (bk.Ep.map ι).IsRoot y := by
    intro z' hz' y hy
    have hnz' : ‖z'‖ = r := (conj l bk.a z z' hz').trans hz
    have hz'Q : (Q.map ι).IsRoot z' := by
      obtain ⟨c, hc⟩ := hmdvd
      rw [Polynomial.IsRoot, ← haev, hc, map_mul, hz', zero_mul]
    have hyE : ((bk.Ep ^ M * P).map ι).IsRoot y := by
      have h4 : ((Polynomial.expand (Wq l bk.a) l Q).map ι).IsRoot y := by
        rw [Polynomial.IsRoot, Polynomial.map_expand, Polynomial.expand_eval, hy]
        exact hz'Q
      obtain ⟨c, hc⟩ := h2
      rw [Polynomial.IsRoot, hc, Polynomial.map_mul, Polynomial.eval_mul, h4.eq_zero, zero_mul]
    have hyr : r < ‖y‖ := by
      by_contra hle
      push_neg at hle
      have h5 : ‖y‖ ^ l = r := by rw [← norm_pow, hy, hnz']
      have h6 : r ^ l < r := pow_lt_self_of_lt_one₀ hr0 hr1 (Fact.out : l.Prime).one_lt
      have h7 : ‖y‖ ^ l ≤ r ^ l := pow_le_pow_left₀ (norm_nonneg _) hle l
      linarith
    have hyP : ¬ Pι.IsRoot y := fun h => absurd (hmax y h) (not_le.2 hyr)
    rw [Polynomial.IsRoot, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval_mul, Polynomial.eval_pow] at hyE
    have h8 := (mul_eq_zero.1 hyE).resolve_right hyP
    rcases Nat.eq_zero_or_pos M with hM | hM
    · rw [hM, pow_zero] at h8; exact absurd h8 one_ne_zero
    · exact (pow_eq_zero_iff hM.ne').1 h8
  have hirr := irr l bk.a bk.Ep bk.monic bk.deg_pos bk.dvd_coeff bk.coeff_zero
  have hc := expandCoeff l bk.a bk.Ep bk.monic hirr z hz0 key
  obtain ⟨i, hi, hci⟩ := bk.not_expand
  exact hci (hc i hi)

end GlobalTheory.LemZ
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos_lt (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)

theorem complete_max (bk : BK K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Wq l bk.a)) (Wq l bk.a) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact hm ▸ inferInstance

theorem dvd_E (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    bk.E ∣ s := by
  haveI := complete_max bk
  have hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff bk.Ep.natDegree) h0
    rw [PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one,
      map_zero] at h1
    exact one_ne_zero h1
  have e1 := s.eq_mul_weierstrassDiv_add_weierstrassMod hg
  set r := s %ʷ bk.E
  have e2 := Polynomial.modByMonic_add_div r bk.Ep
  have e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) +
      ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    conv_lhs => rw [e1, ← e2]
    rw [Polynomial.coe_add, Polynomial.coe_mul]
    simp only [BK.E]; ring
  have h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    have : ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) =
        s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) := by
      rw [eq_sub_iff_add_eq, add_comm, ← e3]
    rw [this, map_sub, map_mul]
    exact dvd_sub h (dvd_mul_right _ _)
  have h4 := GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3
  rw [e3, h4, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

theorem dvd_X (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ X ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    (X : bk.S) ∣ s := by
  rw [PowerSeries.X_dvd_iff]
  have hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀ := by
    rw [PowerSeries.constantCoeff_X, map_zero, norm_zero]; exact NNReal.coe_nonneg _
  have hm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1)
    (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz
  rw [map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul] at h1
  exact (GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)

theorem toDisc_inj (bk : BK K) : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) := by
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  exact (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀
    (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1

theorem mem_nzd (bk : BK K) {x : bk.DS bk.ρ₀} (hx : x ≠ 0) : x ∈ nonZeroDivisors (bk.DS bk.ρ₀) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))

theorem dvd_E_pow (bk : BK K) (m : ℕ) : ∀ s : bk.S,
    toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ toDisc l (X : bk.S) bk.ρ₀ s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; rw [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro s h
    obtain ⟨s', rfl⟩ := dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)
    obtain ⟨z, hz⟩ := h
    have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
      bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))
    rw [map_mul, pow_succ', mul_assoc] at hz
    have := (mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' ⟨z, this⟩)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem lift (bk : BK K) (g : bk.S) (hreg : toDisc l (X : bk.S) bk.ρ₀ g ∈ nonZeroDivisors (bk.DS bk.ρ₀))
    (hdiv : ∀ s : bk.S, toDisc l (X : bk.S) bk.ρ₀ g ∣ toDisc l (X : bk.S) bk.ρ₀ s → g ∣ s)
    (a : Ainf l) (h : bk.iS g ∣ bk.iA a) : bk.ev g ∣ a := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨h0, h1⟩ := ρ₀_pos_lt bk
  have hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0
  have hjm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj
  obtain ⟨cD, hc1, hc2, -, hc4, -⟩ :=
    GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm
  obtain ⟨y, hy⟩ := h
  have hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g) := (hjm.ext g).symm
  have hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y := by
    intro i
    have e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y := by
      rw [← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]
    obtain ⟨q, hq⟩ := hdiv _ ⟨_, e⟩
    refine ⟨q, hq, ?_⟩
    rw [hq, map_mul] at e
    exact (mul_cancel_left_mem_nonZeroDivisors hreg).1 e
  choose q hq1 hq2 using hq
  classical
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hsmall := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit
    (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1
  have hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := hsmall n
    have hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r :=
      (hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_
    have h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r := by rw [hq2 i]; exact hlt.le
    have h6 := hr' (q i) h5
    rwa [Ideal.map_id] at h6
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n := fun n i hi => by
    simpa [F] using hi
  let I : Ideal (Ainf l) := bk.J.map bk.ev
  have key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n := fun n i hi => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hF n i hi)
  let f : ℕ → Ainf l := fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i
  have hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hn => hi (Ideal.pow_le_pow_right hmn hn)
  have hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    have e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i := by
      simp only [f]
      rw [← Finset.sum_sdiff (hmono hmn)]; ring
    rw [e]
    refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))
    exact (Finset.mem_sdiff.1 hi).2
  haveI : IsAdicComplete I (Ainf l) := TB.complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, hsm]
  have happ := TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)
  rw [Ideal.map_pow] at happ
  have hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n := by
    simp only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]
  rw [hs] at happ
  have hLn := hL n
  rw [SModEq.sub_mem, hsm] at hLn
  have e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L) := by ring
  rw [e]
  exact add_mem happ (Ideal.mul_mem_left _ _ hLn)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP

theorem ainf_dvd_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l),
    (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  intro l _ K bk a
  have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
    bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  have hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  refine ⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩
  rw [← map_pow] at h ⊢
  refine DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h
  · rw [map_pow]; exact pow_mem (DiscDvd.mem_nzd bk hE) m
  · rwa [map_pow] at hs

end GlobalTheory.BSP
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section

namespace GlobalTheory.UseLoc.TwistCrysW

theorem isTwistRep_twist (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) :
    IsTwistRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (repV C (twistM (locOC C M) θ)) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  have hent : ∀ a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g) a b =
      algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (TruncatedSeriesCountingIdentities.locC C M g) a b := by
    intro a b
    change algebraMap ↥(OL C.LL) ↥C.LL.1 (((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * (locOC C M g) a b) = _
    rw [map_mul]
    rfl
  change (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec v =
    algebraMap ↥(OL C.LL) ↥C.LL.1 ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) • (TruncatedSeriesCountingIdentities.locC C M g).mulVec v
  funext a
  simp only [Matrix.mulVec, dotProduct, hent, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem isCrys_and_multV : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) → IsCrys (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) → IsCrys (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) ∧ ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (b : ℤ), multV (Br.PD D.loc D.nbr i w hw) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b ≠ 0 → ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (repV C (twistM (locOC C M) θ)) τ (a + b) = multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a := by
  intro D i w hw C k M θ hM hθ
  have key := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) (Fin k → ↥C.LL.1) (repV C (twistM (locOC C M) θ))
    (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ) (isTwistRep_twist D i w hw C k M θ) hθ hM
  refine ⟨key.1, fun τ b hb a => key.2 τ a b ?_⟩
  exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc _) (D.locA _) (D.locT _) (D.nbr i w hw).Kw C.LL
    ↥C.LL.1 (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ)) τ b).2.2.2 hb

end GlobalTheory.UseLoc.TwistCrysW
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem GlobalTheory.CrysPrism.isAdicComplete_Sd : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact GlobalTheory.CrysPrism.Compl.isAdicComplete_of t e (GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O), (∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) → toOB l O x ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | exact GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | (intros; apply GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  first | exact @GlobalTheory.BK.GcdCore.one_mem | exact GlobalTheory.BK.GcdCore.one_mem | (intros; apply GlobalTheory.BK.GcdCore.one_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ (n : ℕ) (d : Fin n → P.D) (c : Fin n → ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))), (∀ k, P.xi (d k) ∈ P.MMl) ∧ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e i (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) ∧ ¬ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e (i + 1) (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) := by
  first | exact @GlobalTheory.BKGal.JumpDR.Horiz.main | exact GlobalTheory.BKGal.JumpDR.Horiz.main | (intros; apply GlobalTheory.BKGal.JumpDR.Horiz.main <;> assumption)
end
