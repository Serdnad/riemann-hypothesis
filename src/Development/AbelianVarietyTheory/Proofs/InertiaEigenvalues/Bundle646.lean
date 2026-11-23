module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle097
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle571
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainFinal
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsVanishAtPrimeOfAdmissible
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle615
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle008
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle012
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.Algebra.Algebra.ZMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobAction

open GlobalTheory.BKReal

theorem galois_pow_frobenius : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l),
    ∃ m : ZMod a, ∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val := by
  intro l hl a _ g
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h1 := one_lt_pow_l l a
  have hmem : ∀ y : Fq l a, Per.σF g (Fq.val l a y) ∈ resSub l a := fun y => by
    rw [mem_resSub, ← map_pow, ← map_pow, Fq.pow_card]
  let φ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) hmem
  have hφ : ∀ y, Fq.val l a (φ y) = Per.σF g (Fq.val l a y) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ _
  haveI : Fintype (Fq l a) := Fintype.ofFinite _
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { φ with
      commutes' := fun r => by
        haveI : NeZero l := ⟨hl.out.ne_zero⟩
        obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective r
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe, map_natCast] }
  have hb : Function.Bijective ψ := Finite.injective_iff_bijective.1 ψ.toRingHom.injective
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod l) (Fq l a)).2
    (AlgEquiv.ofBijective ψ hb)
  have hfr : ∀ (k : ℕ) (y : Fq l a), (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod l) (Fq l a) ^ k) y =
      y ^ l ^ k := fun k y => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card,
        ← pow_mul, ← pow_succ]
  have hφz : φ z = z ^ l ^ (n : ℕ) := by
    have := congrArg (fun e : Fq l a ≃ₐ[ZMod l] Fq l a => e z) hn
    simp only [hfr] at this
    exact this.symm
  have hrank : Module.finrank (ZMod l) (Fq l a) = a := by
    have h2 := Module.card_eq_pow_finrank (K := ZMod l) (V := Fq l a)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, card_Fq] at h2
    exact (Nat.pow_right_injective hl.out.two_le h2).symm

  have key : ∀ y : OCb l, ((PreTilt.untilt (Per.σF g y) : Per.OC l) : ℂ_[l]) =
      Per.σC g ((PreTilt.untilt y : Per.OC l) : ℂ_[l]) := fun y => by
    rw [GlobalTheory.RingBasics.untilt_σF]
    exact GlobalTheory.RingIface.sigO_coe l g _
  have hu := GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz
  have hgω : g ω = ω ^ l ^ (n : ℕ) := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    have h3 := key (Fq.val l a z)
    rw [← hφ, hφz, map_pow, map_pow, SubmonoidClass.coe_pow, hu, GlobalTheory.RingBasics.σC_coe] at h3
    rw [map_pow]
    exact h3.symm
  refine ⟨((n : ℕ) : ZMod a), fun x hx => ?_⟩
  have hval : (((n : ℕ) : ZMod a)).val = n := ZMod.val_natCast_of_lt (lt_of_lt_of_eq n.2 hrank)
  rw [hval]
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, zero_pow (pow_pos hl.out.pos _).ne']
  · have h4 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
    haveI : NeZero (l ^ a - 1) := ⟨by omega⟩
    obtain ⟨k, -, rfl⟩ := hω.eq_pow_of_pow_eq_one h4
    rw [map_pow, hgω, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory.FrobAction
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MinpolyKummerUr

open Polynomial

theorem minpoly_eq {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 0 < M) {ρ : Om l}
    (hρ : ρ ^ M = -(l : Om l)) :
    minpoly (↥(MaximalUnramifiedExtension l)) ρ = Polynomial.X ^ M + Polynomial.C ((l : ℕ) : ↥(MaximalUnramifiedExtension l)) := by
  set F := MaximalUnramifiedExtension l
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hQ : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).Monic := by
    apply Polynomial.monic_X_pow_add_C _ hM.ne'
  have hQdeg : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).natDegree = M := by
    rw [Polynomial.natDegree_X_pow_add_C]
  have haeval : Polynomial.aeval ρ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)) = 0 := by
    simp [hρ]
  have hint : IsIntegral F ρ := by
    refine ⟨_, hQ, ?_⟩
    rwa [← Polynomial.aeval_def]
  have hdvd : minpoly F ρ ∣ Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F) := minpoly.dvd _ _ haeval
  have hmon := minpoly.monic hint
  have hpos : 0 < (minpoly F ρ).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly F ρ).natDegree ≤ M := by
    rw [← hQdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hQ.ne_zero

  have hnρ : ‖ρ‖ ^ M = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hρ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  set P := (minpoly F ρ).map (algebraMap F (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hroots : ∀ a ∈ P.roots, ‖0 - a‖ = ‖ρ‖ := by
    intro a ha
    have h1 : P ∣ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : ((Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))).IsRoot a :=
      (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ M = -(l : Om l) := by
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ M = ‖ρ‖ ^ M := by
      rw [← norm_pow, ← norm_pow, h3, hρ]
    rw [zero_sub, norm_neg]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖ρ‖ ^ (minpoly F ρ).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap F (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖ρ‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = (((minpoly F ρ).eval 0 : F) : Om l) := by
    rw [hP, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
    rfl
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hρ
    have : ((l : ℕ) : Om l) ≠ 0 := by
      intro h
      have := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l (l := l)
      rw [h, norm_zero] at this
      exact (inv_pos.2 hl0).ne this
    exact this (neg_eq_zero.1 hρ.symm)
  have hnρpos : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hy0 : (((minpoly F ρ).eval 0 : F) : Om l) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hnρpos _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow ((minpoly F ρ).eval 0 : F).2 hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (M : ℤ)) = (l : ℝ) ^ (-((minpoly F ρ).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hnρ, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (M : ℤ) = -((minpoly F ρ).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 hl1.ne' h8
  have h10 : (M : ℤ) ∣ ((minpoly F ρ).natDegree : ℤ) := ⟨-m, by linarith⟩
  have hdeg : (minpoly F ρ).natDegree = M :=
    le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hQ hdvd (by rw [hdeg, hQdeg])).symm

theorem aeval_mul_root (l : ℕ) [Fact l.Prime] (M : ℕ) : 0 < M → ∀ (ρ ξ : Om l),
    ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  intro hM ρ ξ hρ hξ
  rw [minpoly_eq hM hρ]
  simp [mul_pow, hξ, hρ]

end GlobalTheory.MinpolyKummerUr
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaDeg
open Polynomial

theorem natDegree_minpoly_root_neg_l : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  intro l _ N π hN hπ E _ _ hE
  have hl0 : (0 : ℝ) < l := by linarith [Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)]
  set Q : E[X] := Polynomial.X ^ N + Polynomial.C ((l : ℕ) : E) with hQ
  have hQm : Q.Monic := by
    rw [hQ]; exact monic_X_pow_add_C _ hN.ne'
  have hQr : aeval π Q = 0 := by
    rw [hQ]; simp [hπ]
  have hint : IsIntegral E π := ⟨Q, hQm, by rwa [aeval_def] at hQr⟩
  have hdvd : minpoly E π ∣ Q := minpoly.dvd _ _ hQr
  have hQdeg : Q.natDegree = N := by rw [hQ]; exact natDegree_X_pow_add_C
  have hle : (minpoly E π).natDegree ≤ N := by
    rw [← hQdeg]; exact natDegree_le_of_dvd hdvd hQm.ne_zero
  have hpos : 0 < (minpoly E π).natDegree := minpoly.natDegree_pos hint
  have hmon := minpoly.monic hint
  set P := (minpoly E π).map (algebraMap E (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hπn : ‖π‖ ^ N = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hπ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  have hroots : ∀ a ∈ P.roots, ‖a‖ = ‖π‖ := by
    intro a ha
    have h1 : P ∣ Q.map (algebraMap E (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : (Q.map (algebraMap E (Om l))).IsRoot a := (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ N = -(l : Om l) := by
      rw [hQ] at h2
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ N = ‖π‖ ^ N := by
      rw [← norm_pow, h3, ← hπ, norm_pow]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖π‖ ^ (minpoly E π).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap E (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖π‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = algebraMap E (Om l) ((minpoly E π).eval 0) := by
    rw [hP, Polynomial.eval_map, ← map_zero (algebraMap E (Om l)), Polynomial.eval₂_at_apply]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm, neg_eq_zero] at hπ
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hπ
  have hρ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hy0 : algebraMap E (Om l) ((minpoly E π).eval 0) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hρ _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow (hE ((minpoly E π).eval 0)) hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (N : ℤ)) = (l : ℝ) ^ (-((minpoly E π).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hπn, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (N : ℤ) = -((minpoly E π).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 (Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)).ne' h8
  have h10 : (N : ℤ) ∣ ((minpoly E π).natDegree : ℤ) := ⟨-m, by linarith⟩
  exact le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))

end GlobalTheory.InertiaDeg
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.InertiaLift


open ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem unr_inf_le {l : ℕ} [Fact l.Prime] (F K'' : IntermediateField ℚ_[l] (Om l))
    (hF : FiniteDimensional ℚ_[l] F) (hK : FiniteDimensional ℚ_[l] K'') (hFK : F ≤ K'') :
    (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' ≤ F ⊔ (K'' ⊓ MaximalUnramifiedExtension l) := by
  set N := (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' with hNdef
  have hN : FiniteDimensional ℚ_[l] N :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_right : N ≤ K'')).toLinearMap
      (IntermediateField.inclusion (inf_le_right : N ≤ K'')).injective
  have hNur : N ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l F := by
    rw [Kur_eq hF]
    refine inf_le_left.trans (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) F)
    rintro x ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩
  obtain ⟨n, hn, hNn⟩ := exists_le_Kn_of_le_Kur hF hN hNur
  have hFN : F ≤ N := le_inf le_sup_left hFK
  have hdvd : Module.finrank ℚ_[l] F ∣ Module.finrank ℚ_[l] N :=
    IntermediateField.finrank_dvd_of_le_right hFN
  have hpos : 0 < Module.finrank ℚ_[l] N := Module.finrank_pos
  have hFpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
  set d := Module.finrank ℚ_[l] N / Module.finrank ℚ_[l] F
  have hd : 0 < d := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hFpos
  have hNeq : N = Kn l F d := eq_Kn_of_norm l F hF hFN hd (Nat.div_mul_cancel hdvd).symm
    (fun x hx => norm_Kn l F hF hn (hNn hx))
  rw [hNeq]
  refine UnramifiedExtensions.Kn_le F le_sup_left fun ζ hζ => (le_sup_right : K'' ⊓ MaximalUnramifiedExtension l ≤ _) ⟨?_, ?_⟩
  · have h1 : ζ ∈ N := by rw [hNeq]; exact mem_Kn_of_pow l F hζ
    exact h1.2
  · refine IntermediateField.subset_adjoin _ _ ⟨_, ?_, UnramifiedExtensions.not_dvd_qK_pow_sub_one F hF hd, hζ⟩
    have := one_lt_qK l F hF
    have : 1 < qK l F ^ d := Nat.one_lt_pow hd.ne' this
    omega

end GlobalTheory.InertiaLift

namespace GlobalTheory.InertiaLift

theorem exists_mul_of_fixes {l : ℕ} [Fact l.Prime] (M K'' : IntermediateField ℚ_[l] (Om l))
    (hK : FiniteDimensional ℚ_[l] K'')
    (hconj : ∀ s ∈ M.fixingSubgroup, ∀ k ∈ K''.fixingSubgroup, s⁻¹ * k * s ∈ K''.fixingSubgroup)
    (h : GQ l) (hh : ∀ x ∈ M ⊓ K'', h x = x) :
    ∃ i ∈ M.fixingSubgroup, i⁻¹ * h ∈ K''.fixingSubgroup := by
  let T : Subgroup (GQ l) :=
    { carrier := {g | ∃ s ∈ M.fixingSubgroup, s⁻¹ * g ∈ K''.fixingSubgroup}
      one_mem' := ⟨1, M.fixingSubgroup.one_mem, by simpa using K''.fixingSubgroup.one_mem⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨s₁, hs₁, hk₁⟩ ⟨s₂, hs₂, hk₂⟩
        refine ⟨s₁ * s₂, M.fixingSubgroup.mul_mem hs₁ hs₂, ?_⟩
        have e : (s₁ * s₂)⁻¹ * (g₁ * g₂) = (s₂⁻¹ * (s₁⁻¹ * g₁) * s₂) * (s₂⁻¹ * g₂) := by group
        rw [e]
        exact K''.fixingSubgroup.mul_mem (hconj s₂ hs₂ _ hk₁) hk₂
      inv_mem' := by
        rintro g ⟨s, hs, hk⟩
        refine ⟨s⁻¹, M.fixingSubgroup.inv_mem hs, ?_⟩
        have e : s⁻¹⁻¹ * g⁻¹ = (s⁻¹)⁻¹ * (s⁻¹ * g)⁻¹ * s⁻¹ := by group
        rw [e]
        exact hconj _ (M.fixingSubgroup.inv_mem hs) _ (K''.fixingSubgroup.inv_mem hk) }
  have hNT : K''.fixingSubgroup ≤ T := fun k hk => ⟨1, M.fixingSubgroup.one_mem, by simpa using hk⟩
  have hMT : M.fixingSubgroup ≤ T := fun s hs => ⟨s, hs, by simpa using K''.fixingSubgroup.one_mem⟩
  have hopen : IsOpen (T : Set (GQ l)) := Subgroup.isOpen_mono hNT (IntermediateField.fixingSubgroup_isOpen K'')
  let Tc : ClosedSubgroup (GQ l) := ⟨T, Subgroup.isClosed_of_isOpen T hopen⟩
  have hfix : IntermediateField.fixedField T ≤ M ⊓ K'' := by
    refine le_inf ?_ ?_
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro x hx s
      exact hx ⟨s.1, hMT s.2⟩
    · rw [← InfiniteGalois.fixedField_fixingSubgroup K'']
      intro x hx s
      exact hx ⟨s.1, hNT s.2⟩
  have hT : h ∈ (IntermediateField.fixedField (Tc : Subgroup (GQ l))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hh x (hfix hx)
  rw [InfiniteGalois.fixingSubgroup_fixedField Tc] at hT
  exact hT

theorem inertia_of_fixes_Kur {l : ℕ} [Fact l.Prime] (i : GQ l) (hi : ∀ x ∈ MaximalUnramifiedExtension l, i x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖i x - x‖ < 1 := by
  have hn : ∀ y : Om l, ‖i y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv i y).symm
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hlt) hlt)
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : i ζ = ζ := hi ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : i x - x = i (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hxζ) hxζ)

theorem lift : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 →
    ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) →
      ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧
        (i : GQ l)⁻¹ * h ∈ GK K'' := by
  intro l _ K' F K'' hnorm hK'' h hF h0
  have hFK : F.1 ≤ K''.1 := hK'' ▸ le_sup_right
  have hfK : FiniteDimensional ℚ_[l] K''.1 := K''.2
  have hfF : FiniteDimensional ℚ_[l] F.1 := F.2

  have h1 : h ∈ (F.1 ⊔ (K''.1 ⊓ MaximalUnramifiedExtension l)).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hF, (IntermediateField.mem_fixingSubgroup_iff _ _).2 h0⟩
  have h2 : ∀ x ∈ (F.1 ⊔ MaximalUnramifiedExtension l) ⊓ K''.1, h x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x (unr_inf_le F.1 K''.1 hfF hfK hFK hx)
  have hconj : ∀ s ∈ (F.1 ⊔ MaximalUnramifiedExtension l).fixingSubgroup, ∀ k ∈ K''.1.fixingSubgroup,
      s⁻¹ * k * s ∈ K''.1.fixingSubgroup := by
    intro s hs k hk
    rw [IntermediateField.fixingSubgroup_sup] at hs
    rw [hK'', IntermediateField.fixingSubgroup_sup] at hk ⊢
    refine ⟨?_, F.1.fixingSubgroup.mul_mem (F.1.fixingSubgroup.mul_mem
      (F.1.fixingSubgroup.inv_mem hs.1) hk.2) hs.1⟩
    have := hnorm.conj_mem k hk.1 s⁻¹
    rw [inv_inv] at this
    exact this
  obtain ⟨i, hi, hik⟩ := exists_mul_of_fixes (F.1 ⊔ MaximalUnramifiedExtension l) K''.1 hfK hconj h h2
  rw [IntermediateField.fixingSubgroup_sup] at hi
  have hiQ : i ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact i.commutes y
  refine ⟨⟨i, hiQ⟩, Subgroup.subset_closure ?_, hi.1, hik⟩
  exact inertia_of_fixes_Kur i ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hi.2)

end GlobalTheory.InertiaLift
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TheoremAFinal

theorem integralityFromMetric_of_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC
  exact Formalism.MainNotions.N.Ln34.integrality_from_metric_of_large_constant D HW F Cm CA CB CK C hC
    (fun l _ K s LL hG T₀ T₁ T₂ ι π h => GlobalTheory.LatExact.W_exact D HW F l K s LL hG T₀ T₁ T₂ ι π h)
    (GlobalTheory.CrysDdR.finrank_DdRE_of_isCrys D) (GlobalTheory.NL.IotaLetterRank.finrank_iota_letter D HW F Cm)

end GlobalTheory.TheoremAFinal
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.invariants_vanish_at_prime_of_admissible : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; H0at S E := by
  first | exact @GlobalTheory.Cyc.InvKilled.invariants_killed | exact GlobalTheory.Cyc.InvKilled.invariants_killed | (intros; apply GlobalTheory.Cyc.InvKilled.invariants_killed <;> assumption)
end

section


theorem _root_.GlobalTheory.T.invIso_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.InvIso := by
  first | exact @GlobalTheory.InvColim.inv_iso | exact GlobalTheory.InvColim.inv_iso | (intros; apply GlobalTheory.InvColim.inv_iso <;> assumption)
end
