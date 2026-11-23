module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerCoefficientRationalMirabolicMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

section

namespace GlobalTheory.UnramifiedCrys

theorem exists_witt_trace_one : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  intro p hp G _ R _ _ _ _ ρ m hm hfin
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  obtain ⟨θ, hθ⟩ : ∃ θ : fixedPow p R m, ∑ x : G ⧸ N, ρ x.out θ ≠ 0 := by
    by_contra hc
    push Not at hc
    have := Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      funext θ
      simp only [one_smul, Finset.sum_apply, Function.comp, Pi.zero_apply]
      exact hc θ) (QuotientGroup.mk 1)
    exact one_ne_zero this
  have hθm : (θ : R) ^ p ^ m = θ := θ.2
  have hsum : ∀ (f : G → WittVector p R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  set t := ∑ x : G ⧸ N, ρ x.out θ with ht
  have htq : t ^ p ^ m = t := by
    rw [ht, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, hθm]
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hu : t ^ (p ^ m - 2) * t = 1 := by
    apply mul_right_cancel₀ hθ
    rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
  have hθN : ∀ n ∈ N, WittVector.map (ρ n).toRingHom (WittVector.teichmuller p (θ : R)) =
      WittVector.teichmuller p (θ : R) := fun n hn => by
    rw [WittVector.map_teichmuller]
    congr 1
    exact hn θ hθm
  set T := ∑ x : G ⧸ N, WittVector.map (ρ x.out).toRingHom (WittVector.teichmuller p (θ : R))
    with hT
  have hTg : ∀ g, WittVector.map (ρ g).toRingHom T = T := fun g => by

    rw [hT, map_sum, ← hsum (fun g => WittVector.map (ρ g).toRingHom
    (WittVector.teichmuller p (θ : R))) (fun g n hn => by
      simp only [wittMap_mul, hθN n hn]) g]
    simp only [wittMap_mul]
  have hT0 : WittVector.constantCoeff T = t := by

    rw [hT, map_sum, ht]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [WittVector.map_teichmuller, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    rfl
  have hcomp := WittVector.isAdicCompleteIdealSpanP (p := p) (k := R)
  have hmem : T * WittVector.teichmuller p (t ^ (p ^ m - 2)) - 1 ∈
      Ideal.span {(p : WittVector p R)} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
      map_mul, map_one, hT0, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
      mul_comm, hu, sub_self]
  have hunit : IsUnit T := by
    have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hmem) 1
    rw [mul_one, sub_add_cancel] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨S, hS⟩ := hunit.exists_left_inv
  have hSg : ∀ g, WittVector.map (ρ g).toRingHom S = S := fun g => by
    have h2 := congrArg (WittVector.map (ρ g).toRingHom) hS
    rw [map_mul, hTg, map_one] at h2
    exact hunit.mul_right_cancel (h2.trans hS.symm)
  refine ⟨S * WittVector.teichmuller p (θ : R), fun g hg => ?_, ?_⟩
  · rw [map_mul, hSg, hθN g hg]
  · rw [finsum_eq_sum_of_fintype]
    simp only [map_mul, hSg]
    rw [← Finset.mul_sum, ← hT, hS]

end GlobalTheory.UnramifiedCrys
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (U : ℤ_[l]) (k : ℕ) (β η : Ainf l), Step AI g U AI.μ k (WittVector.frobenius β - AI.ξ ^ k * β) (WittVector.frobenius η - AI.ξ ^ k * η) → ∃ z : ℤ_[l], Step AI g U AI.π₁ k β (η + algebraMap ℤ_[l] (Ainf l) z * AI.π₁ ^ k) := by
  first | exact @GlobalTheory.ExpStep.main | exact GlobalTheory.ExpStep.main | (intros; apply GlobalTheory.ExpStep.main <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ), 1 ≤ j → j ≤ s → ¬ l ∣ n → ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  first | exact @GlobalTheory.ExpImage.Values.exists_cycVal_eq | exact GlobalTheory.ExpImage.Values.exists_cycVal_eq | (intros; apply GlobalTheory.ExpImage.Values.exists_cycVal_eq <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem io_mem_Lat_of_mem_span {M n : ℕ} {x : Ainf l}
    (hx : x ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI x ∈ Lat AI M n := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.1 hx
  rw [map_add (f := _), mul_comm p]
  refine add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)
  rw [map_mul, map_pow]
  exact FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)

theorem bounded_and_eventually_sub_mem_Lat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ,
    (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧
      ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  intro l _ P AI T b hb M n
  obtain ⟨k, a, ha⟩ := GlobalTheory.BdRQuot.exists_approx T M b hb
  change (l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha
  constructor
  · have h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0 := ⟨a, by simpa using ha⟩
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact (pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0
  · filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg
    rw [← pow_mul_mem_Lat_iff AI (k := k)]
    have h1 := io_mem_Lat_of_mem_span AI hg
    have h2 := FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)
    have h3 := add_mem h1 h2
    rw [map_sub, io_act, map_sub, map_mul, map_pow, map_natCast] at h3
    convert h3 using 1
    ring

end GlobalTheory.ExpImage
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → Continuous (colT ψ (m + 1) f) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_colT_good | exact GlobalTheory.CuspGeneric.continuous_colT_good | (intros; apply GlobalTheory.CuspGeneric.continuous_colT_good <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_adelicRationalPoints_comm : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι → Ad E) × (κ → Ad E) → ℂ), Per ((ratV E ι).prod (ratV E κ)) Φ → avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) = avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_comm | exact GlobalTheory.CuspGeneric.avg_comm | (intros; apply GlobalTheory.CuspGeneric.avg_comm <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_sum_index_fubini : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ → avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_sum_index | exact GlobalTheory.CuspGeneric.avg_sum_index | (intros; apply GlobalTheory.CuspGeneric.avg_sum_index <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_column_law : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Good ψ (m + 1) f → ∀ (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) (g : GA E a), colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast a (m + 1)) y) * colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_blkU_mul | exact GlobalTheory.CuspGeneric.colT_blkU_mul | (intros; apply GlobalTheory.CuspGeneric.colT_blkU_mul <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) → ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a), coefF ψ (m + 1) ξ f (ratGL E a γ * g) = coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  first | exact @GlobalTheory.CuspGeneric.coefF_ratGL_mul | exact GlobalTheory.CuspGeneric.coefF_ratGL_mul | (intros; apply GlobalTheory.CuspGeneric.coefF_ratGL_mul <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family


variable (X) in
abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)



variable {H S d}

end Family

section Record

variable {H : X.Tw → ℕ → Subgroup (GE N)} {S : X.Tw → ℕ → Finset (PlE D.host)} {d : ∀ i M, Fam X i M}

end Record

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

end GlobalTheory.UnivChar

end
end

section

noncomputable section
namespace GlobalTheory.TameInertiaCyclic
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_norm (K : FinExt l) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ a : ℤ, ‖x‖ ^ d = (l : ℝ) ^ a := by
  haveI := K.2
  refine ⟨Module.finrank ℚ_[l] ↥K.1, Module.finrank_pos, fun x hxK hx => ?_⟩
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[l] (PadicAlgCl l) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hn := minpoly.natDegree_pos hi
  have hd : (minpoly ℚ_[l] x).natDegree ∣ Module.finrank ℚ_[l] ↥K.1 := by
    have := minpoly.degree_dvd (K := ℚ_[l]) (x := (⟨x, hxK⟩ : ↥K.1)) (Algebra.IsIntegral.isIntegral _)
    rwa [IntermediateField.minpoly_eq] at this
  obtain ⟨c, hc⟩ := hd
  refine ⟨-((minpoly ℚ_[l] x).coeff 0).valuation * c, ?_⟩
  rw [hc, pow_mul, e, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn.ne',
    Padic.norm_eq_zpow_neg_valuation h0, zpow_mul, zpow_natCast]

theorem exists_gen (K : FinExt l) :
    ∃ π ∈ K.1, π ≠ 0 ∧ ∀ x ∈ K.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π ^ k‖ := by
  obtain ⟨d, hd, H⟩ := exists_pow_norm K
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ x ∈ K.1, x ≠ 0 ∧ ‖x‖ ^ d = (l : ℝ) ^ n}
      add_mem' := by
        rintro a b ⟨x, hx, hx0, ex⟩ ⟨y, hy, hy0, ey⟩
        exact ⟨x * y, mul_mem hx hy, mul_ne_zero hx0 hy0, by
          rw [norm_mul, mul_pow, ex, ey, zpow_add₀ hl0]⟩
      zero_mem' := ⟨1, one_mem _, one_ne_zero, by simp⟩
      neg_mem' := by
        rintro a ⟨x, hx, hx0, ex⟩
        exact ⟨x⁻¹, inv_mem hx, inv_ne_zero hx0, by rw [norm_inv, inv_pow, ex, zpow_neg]⟩ }
  haveI : IsAddCyclic S := AddSubgroup.isAddCyclic S
  obtain ⟨f, hf⟩ := IsAddCyclic.exists_zsmul_surjective (G := S)
  have hfS : (f : ℤ) ∈ S := f.property
  obtain ⟨π, hπ, hπ0, eπ⟩ := hfS
  refine ⟨π, hπ, hπ0, fun x hx hx0 => ?_⟩
  obtain ⟨a, ha⟩ := H x hx hx0
  have haS : a ∈ S := ⟨x, hx, hx0, ha⟩
  obtain ⟨k, hk⟩ := hf ⟨a, haS⟩
  have hk' : k • (f : ℤ) = a := congrArg Subtype.val hk
  subst a
  refine ⟨k, (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hd.ne').1 ?_⟩
  rw [ha, norm_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, eπ, ← zpow_mul,
    smul_eq_mul, mul_comm]

theorem fix_of_near (K : FinExt l) (g : GQ l) (hst : ∀ x ∈ K.1, g x ∈ K.1)
    (hnear : ∀ x ∈ K.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) {N : ℕ} (hN : ¬ l ∣ N)
    (hgN : ∀ x ∈ K.1, (g ^ N) x = x) (y : Om l) (hy : y ∈ K.1) : g y = y := by
  by_contra hne
  have hx0 : g y - y ≠ 0 := sub_ne_zero.2 hne
  have hxK : g y - y ∈ K.1 := sub_mem (hst y hy) hy
  set x := g y - y with hx
  have h1 : ∀ i : ℕ, ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hnear x hxK hx0
  have h2 : ∀ k : ℕ, ‖((g ^ k) y - y) - (k : Om l) * x‖ < ‖x‖ := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
      have e : ((g ^ (k + 1)) y - y) - ((k + 1 : ℕ) : Om l) * x =
          (((g ^ k) y - y) - (k : Om l) * x) + ((g ^ k) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, hx, map_sub]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 k))
  have hmn : ‖(N : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hN)
  have := h2 N
  rw [hgN y hy, sub_self, zero_sub, norm_neg, norm_mul, hmn, one_mul] at this
  exact lt_irrefl _ this

def ratio (g : GQ l) (x : Om l) : OO l :=
  ⟨g x / x, by
    show ‖g x / x‖ ≤ 1
    rw [norm_div, norm_gal]; exact div_self_le_one _⟩

theorem ratio_mul (g : GQ l) (x y : Om l) : ratio g (x * y) = ratio g x * ratio g y :=
  Subtype.ext (by
    show g (x * y) / (x * y) = g x / x * (g y / y)
    rw [map_mul, mul_div_mul_comm])

theorem res_ratio_iff (g : GQ l) {x : Om l} (hx : x ≠ 0) :
    res (ratio g x) = 1 ↔ ‖g x - x‖ < ‖x‖ := by
  rw [← map_one (res (l := l)), res_eq_iff]
  show ‖g x / x - 1‖ < 1 ↔ _
  have : g x / x - 1 = (g x - x) / x := by field_simp
  rw [this, norm_div, div_lt_one (norm_pos_iff.2 hx)]

theorem res_ratio_zpow (g : GQ l) {x : Om l} (hx : x ≠ 0) (h : res (ratio g x) = 1) (k : ℤ) :
    res (ratio g (x ^ k)) = 1 := by
  induction k using Int.induction_on with
  | zero => rw [res_ratio_iff g (by simp)]; simp
  | succ k ih => rw [zpow_add_one₀ hx, ratio_mul, map_mul, ih, h, one_mul]
  | pred k ih =>
    have e : x ^ (-(k : ℤ)) = x ^ (-(k : ℤ) - 1) * x := by
      rw [← zpow_add_one₀ hx, sub_add_cancel]
    rwa [e, ratio_mul, map_mul, h, mul_one] at ih

theorem map_mem_Kur (g : GQ l) {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : g c ∈ MaximalUnramifiedExtension l := by
  unfold MaximalUnramifiedExtension at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hlm, hx⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  | algebraMap x => rw [g.commutes]; exact (MaximalUnramifiedExtension l).algebraMap_mem x
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact (MaximalUnramifiedExtension l).add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact (MaximalUnramifiedExtension l).inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact (MaximalUnramifiedExtension l).mul_mem hx hy

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

end GlobalTheory.TameInertiaCyclic
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.cocycle_unramified_outside_vanish_on_kernel : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ContAction ρ → ∀ (A : Formalism.GaloisCohomology.Places F Ω) (S : Set (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ∀ m, ρ σ m = m) → ∀ x : Z1 ρ, (∀ v ∉ S, resH1 ρ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ n ∈ NS Ω S, x.1 n = 0 ∧ ∀ m, ρ n m = m := by
  first | exact @GlobalTheory.UnramCocycle.vanish_on_NS | exact GlobalTheory.UnramCocycle.vanish_on_NS | (intros; apply GlobalTheory.UnramCocycle.vanish_on_NS <;> assumption)
end
