module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle002
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
public import GroundTheory.PAdicHodge.Bundle014
public import GroundTheory.PAdicHodge.FundamentalSeqSurj
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section Abstract

theorem onto_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C}
    (hk : Function.Injective k) {G : C →+* C} {g : A →+* A} (hG : ∀ x, G (k x) = k (g x))
    {p m n : ℕ} {a : A} {y : C} (ha : k a = k (p : A) ^ m * y) (hy : G y = (p : C) ^ n * y) :
    g a = (p : A) ^ n * a := by
  apply hk
  rw [← hG, map_mul, map_pow, ha, map_mul, map_pow, map_natCast, map_natCast, hy]
  ring

theorem onto_fixed {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {F : B →+* B}
    {g : A →+* A} (hF : ∀ x, F (f x) = f (g x)) {p t a : A} (hf : IsFrac f p t) (hp : g p = p)
    (ht : g t = p * t) (m : ℕ) {n : ℕ} (ha : g a = p ^ n * a) :
    ∃ x : B, F x = x ∧ f p ^ m * f t ^ n * x = f a := by
  obtain ⟨x, hx⟩ := ((hf.1.pow m).mul (hf.2.1.pow n)).exists_right_inv
  have e : f p ^ m * f t ^ n * (x * f a) = f a := by rw [← mul_assoc, hx, one_mul]
  refine ⟨x * f a, ?_, e⟩
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, hp, ht, ha, map_mul f, map_mul f,
    map_pow f] at h1
  refine ((hf.1.pow m).mul ((hf.1.mul hf.2.1).pow n)).mul_left_cancel (h1.trans ?_)
  conv_lhs => rw [← e]
  ring

theorem onto_cancel {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) {p a : A} (hp : c p ≠ 0) {m : ℕ}
    {y : C} (ha : k a = k p ^ m * y) {z : E} (h : c a = c p ^ m * z) : z = I y := by
  have h1 := congrArg I ha
  rw [map_mul, map_pow, hI, hI, h] at h1
  exact mul_left_cancel₀ (pow_ne_zero m hp) h1

theorem onto_injective {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) (hc : Function.Injective c) :
    Function.Injective k := fun x y e => hc (by rw [← hI, ← hI, e])

theorem away_exists_self {A : Type} [CommRing A] {a : A} (y : Localization.Away a) :
    ∃ (k : ℕ) (x : A), algebraMap A (Localization.Away a) x =
      algebraMap A (Localization.Away a) a ^ k * y :=
  away_exists (RingHom.id _) _ (fun _ => rfl) y

end Abstract

section Concrete

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem onto_plus {y : ACris.BCrisPlus ℂ_[l] l} {n : ℕ}
    (hy : ACris.phiPlus ℂ_[l] l y = (l : ACris.BCrisPlus ℂ_[l] l) ^ n * y) :
    ∃ x : Per6.Bcris l, Per6.φB l x = x ∧ cD l (Per6.tA l) ^ n * ιCD l x = invPlusD l y := by
  obtain ⟨m, a, ha⟩ := away_exists_self (a := (l : ACris.ACris ℂ_[l] l)) y
  have hmap := invPlusD_algebraMap (l := l)
  have hinj := onto_injective (I := invPlusD l) (c := cD l) hmap (cD_injective l)
  have h1 := onto_eigen (G := ACris.phiPlus ℂ_[l] l) (p := l) hinj
    (ACris.phiPlus_algebraMap (K := ℂ_[l]) (p := l)) ha hy
  obtain ⟨x, hx, e⟩ := onto_fixed (φB_cB (l := l)) (cB_isFrac l)
    (ACris.phi_natCast_p ℂ_[l] l) frob_phi_tA m h1
  exact ⟨x, hx, onto_cancel (I := invPlusD l) (c := cD l) hmap
    (cD_l_ne_zero l) ha (inv_map_frac (ιCD_fac l) e)⟩

theorem cD_tA_eq : cD l (Per6.tA l) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (epsilon l) untilt_epsilon) :=
  cD_tA l

theorem fund_onto (z : Per6.BdR l) : ∃ x : Per6.Bcris l, Per6.φB l x = x ∧
    ∃ c : Per6.BdRp l, ιCD l x - z = algebraMap (Per6.BdRp l) (Per6.BdR l) c := by
  obtain ⟨n, w, hs⟩ := ACris.exists_mul_pow_fontaineT_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one z
  obtain ⟨y, hy, hyw⟩ := ACris.exists_phiPlus_eq_pow_iotaPlus_sub_mem (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one (m := n) (n := n) le_rfl w
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyw
  obtain ⟨x, hx, e⟩ := onto_plus hy
  have he := (congrArg (fun t : Per6.BdR l => t ^ n * ιCD l x) (cD_tA_eq (l := l))).symm.trans e
  exact ⟨x, hx, c, ACris.sub_eq_map_of_pow_mul (algebraMap (Per6.BdRp l) (Per6.BdR l))
    (T := fontaineT (epsilon l) untilt_epsilon) (a := ACris.iotaPlus ℂ_[l] l y)
    (algebraMap_tBdR_ne_zero (p := l)) he hs hc⟩

section Eps

variable {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)




end Eps


end Concrete

end PositivityTheory.LocInh
end
end

section

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem tiedA_inv_of_theta {y : Per6.BdRp l} (h : Per6.θD l y ≠ 0) : ∃ z, y * z = 1 := by
  have h1 : y ∉ IsLocalRing.maximalIdeal (Per6.BdRp l) := by
    rw [← filq_ker_eq]
    exact h
  exact (IsLocalRing.notMem_maximalIdeal.1 h1).exists_right_inv

variable {P : LocPrime l} {AI : LocAinf l P}

theorem tiedA_inv (T : LocTied6 l P AI) (K : FinExt l) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) (hy : Per6.θD l y ≠ 0) :
    ∃ u ∈ (P.PD K).Fil 0, x * u = 1 := by
  obtain ⟨z, hz⟩ := tiedA_inv_of_theta hy
  have e := T.eD.apply_symm_apply (algebraMap (Per6.BdRp l) (Per6.BdR l) z)
  refine ⟨_, (tie_fil_zero T K _).2 ⟨z, e⟩, T.eD.injective ?_⟩
  rw [map_mul, e, h, ← map_mul, hz, map_one, map_one]

theorem tiedA_ι_injective (P : LocPrime l) : Function.Injective P.ιB := fun a b h =>
  (P.PD (MainNotions.LocalSituation.botExt l)).ι_inj (((P.PD_ι _ a).trans h).trans (P.PD_ι _ b).symm)

theorem tiedA_φ_injective (P : LocPrime l) : Function.Injective P.φB := fun a b h =>
  (P.PD (MainNotions.LocalSituation.botExt l)).φ_inj (((P.PD_φ _ a).trans h).trans (P.PD_φ _ b).symm)

theorem tiedA_isField (T : LocTied6 l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (Field.toIsField (Per6.BdR l))

variable (K : IntermediateField ℚ_[l] (PadicAlgCl l))

variable [FiniteDimensional ℚ_[l] K]

end SlopeTestRemainingChoices

theorem tied_field : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied6 l P AI →
    IsField P.R.BdR ∧ IsDomain P.R.B ∧ Function.Injective P.ιB ∧ Function.Injective P.φB ∧
      ∀ (K : FinExt l) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → x ∉ (P.PD K).Fil 1 →
        ∃ y ∈ (P.PD K).Fil 0, x * y = 1 := by
  intro l _ P AI T
  have hF := tiedA_isField T
  have hD : IsDomain P.R.BdR := hF.isDomain
  refine ⟨hF, (tiedA_ι_injective P).isDomain P.ιB.toRingHom, tiedA_ι_injective P,
    tiedA_φ_injective P, fun K x h0 h1 => ?_⟩
  obtain ⟨y, hy⟩ := (tie_fil_zero T K x).1 h0
  refine tiedA_inv T K hy fun h => h1 ((filq_tie_fil T K 1 hy).2 ?_)
  rw [pow_one]
  exact h

end PositivityTheory.LocInh
end
end
