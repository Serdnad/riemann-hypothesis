module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSequenceEtaleTateTwist
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle511
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle692
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle693
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Formalism.PieriBlockIdeals.Bundle001
import Formalism.PieriBlockIdeals.LemmaWFromLattice

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AcycRes

theorem coneBij {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J)
    (h : ∀ m, Subsingleton (CohomologyClass K (mappingCone f) m)) (n : ℤ) : Function.Bijective (cpush K f n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f m
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f (m + 1)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h3 x).1 hx
    rw [(h m).elim y 0, map_zero]
  · intro y
    exact (h1 y).1 ((h (m + 1)).elim _ _)

theorem subOfIso {R : Type} [CommRing R] {A B : Shv R} (e : A ≅ B) (M : Cx R) (n : ℤ)
    (h : Subsingleton (CohomologyClass (sgl B) M n)) : Subsingleton (CohomologyClass (sgl A) M n) := by
  obtain ⟨hid, hcomp, -, -, -⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.hom) M n
      (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n z) = z := by
    intro z
    rw [← hcomp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n x)]

theorem discFree {R : Type} [CommRing R] (P : PSh) (X : Shv R) (i : ℤ) (h : Subsingleton (H R (disc.obj P) X i)) :
    Subsingleton (CohomologyClass (sgl ((free R).obj P)) (res R X) i) := by
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨hid, hcomp, -, -, hhtpy⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull (e P).hom (res R X) i (cpull (e P).inv (res R X) i z) = z := by
    intro z
    rw [← hcomp, (hhtpy _ _ ⟨(e P).homotopyHomInvId⟩ (res R X) i).1]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull (e P).inv (res R X) i x)]

end GlobalTheory.EtC.AcycRes


open GlobalTheory.EtC.AcycRes in
theorem GlobalTheory.EtC.acycRes_computes : ∀ (R : Type) [CommRing R] (F : Shv R) (C : Cx R) [C.IsStrictlyGE 0] (ε : sgl F ⟶ C) [QuasiIso ε] (u : C ⟶ res R F), ε ≫ u = resAug F → (∀ (t : ℤ) (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) (C.X t) n)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains R).obj E) u n) := by
  intro R _ F C _ ε _ u hu hC E n
  obtain ⟨-, hinj, hge, hqa, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  have : QuasiIso (ε ≫ u) := by rw [hu]; exact hqa
  have : QuasiIso u := quasiIso_of_comp_left ε u
  have : ((chains R).obj E).IsStrictlyLE 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R).1 E
  have : (mappingCone u).IsStrictlyGE (-1) := isStrictlyGE_mappingCone u 0 0 (-1)
  apply coneBij
  intro m
  apply GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero R _ _ _ m
  intro p k hp
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
  apply subOfIso (chainsXIso R E q)
  apply GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow R _ _ (-1) (GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso R u)
  intro t i hi
  apply GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton R _ u hinj _ t i hi
  intro t' i' hi'
  exact discFree _ _ _ (hC t' _ i' hi')
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummer_sequence_etale_tateTwist : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, Mono κ ∧ κ ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map κ a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.kummer_sequence) | (exact GlobalTheory.EtC.kummer_sequence) | (intros; apply GlobalTheory.EtC.kummer_sequence  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_of_locExact_supp) | (exact GlobalTheory.EtC.subsingleton_of_locExact_supp) | (intros; apply GlobalTheory.EtC.subsingleton_of_locExact_supp  <;> assumption)
end

section

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.PDiv

theorem exists_pow_eq_of_integers {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {n : ℕ} (hn : 0 < n) (a : O) : ∃ b : O, b ^ n = a := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn
  have h1 : v c ^ n ≤ 1 := by
    rw [← map_pow, hc]
    exact hv.map_le_one a
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)
  exact ⟨b, hv.hom_inj (by rw [map_pow, hc])⟩

theorem omega_finite_projective (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) :
    Module.Finite O G.omega ∧ Module.Projective O G.omega := by
  have : IsDomain O := hv.hom_inj.isDomain _
  have : ValuationRing O := ValuationRing.of_integers v hv
  have hp : (p : O) ≠ 0 := fun h => by
    have := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.1 this)
  have htf : ∀ w : G.omega, (p : O) • w = 0 → w = 0 :=
    GlobalTheory.T.pDivGroup_omega_noPTorsion_of_cotangent_injective p O G fun n => GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq O _ _ (G.mulP n)
      (GlobalTheory.T.mulP_mem_sq_counit_ker p O hp Fact.out (exists_pow_eq_of_integers hv (Fact.out : p.Prime).pos) G n)
  have htfk : ∀ (k : ℕ) (w : G.omega), (p : O) ^ k • w = 0 → w = 0 := fun k => by
    induction k with
    | zero => intro w hw; rwa [pow_zero, one_smul] at hw
    | succ k ih => intro w hw; exact htf w (ih _ (by rw [← mul_smul, ← pow_succ, hw]))
  have : Module.Finite O G.omega := by
    have h := Module.Finite.equiv (G.omegaQuotEquiv 1).symm
    rw [pow_one] at h
    exact GlobalTheory.finite_of_isHausdorff_of_finite_quotient (Ideal.span {(p : O)}) _
  have : Module.Flat O G.omega := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro w ⟨⟨a, ha⟩, hw⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have : ∃ k, a ∣ (p : O) ^ k := by
      by_contra! hk
      refine ha0 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) a fun k => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact (ValuationRing.dvd_total _ _).resolve_left (hk k)
    obtain ⟨k, c, hc⟩ := this
    have hw' : a • w = 0 := hw
    exact htfk k w (by rw [hc, mul_comm, mul_smul, hw', smul_zero])
  have : Module.Free O G.omega := Module.free_of_flat_of_isLocalRing
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.PDiv
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.pDivGroup_idempotent_split_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧ ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  first | exact @GlobalTheory.PDivGroup.idempotent_split | exact GlobalTheory.PDivGroup.idempotent_split | (intros; apply GlobalTheory.PDivGroup.idempotent_split <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzRamified

theorem norm_int_eq_one {l : ℕ} [Fact l.Prime] {z : ℤ} (h : ¬ (l : ℤ) ∣ z) : ‖(z : ℂ_[l])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

theorem norm_bound {l : ℕ} [Fact l.Prime] (W S P : ℂ_[l]) (hl : 4 < l) (hW : W ^ 2 = -(l : ℂ_[l]))
    (hP : ‖12 * P‖ ≤ 1) (hS : ‖((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P‖ ≤ 1) :
    ‖S‖ ≤ (l : ℝ) ^ (1 / 2 : ℝ) := by
  have hpr : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hpr.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have h12 : ‖(12 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 12 := by
      intro h
      have h' : l ∣ 12 := by exact_mod_cast h
      have h4 : l ∣ 2 ^ 2 * 3 := h'
      rcases (Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    simpa using norm_int_eq_one (l := l) hd
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 2 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    simpa using norm_int_eq_one (l := l) hd
  have hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hW, norm_neg, hn]
  have hW1 : ‖W‖ < 1 := by
    have : ‖W‖ ^ 2 < 1 := by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1
    nlinarith [norm_nonneg W]
  have h1W : ‖1 + W‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one,
      max_eq_left hW1.le]
  have hP1 : ‖P‖ ≤ 1 := by rwa [norm_mul, h12, one_mul] at hP
  have hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1 := by
    have e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P := by ring
    have h2W : ‖2 + W‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)
    rw [e, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1
  have hA : ‖W‖ * ‖S‖ ≤ 1 := by
    have e : 2 * W * (1 + W) * S =
        (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P := by
      linear_combination S * hW
    have := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)
    rwa [← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one] at this
  have hsq : ‖S‖ ^ 2 ≤ l := by
    have h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hA
    rw [mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one] at h3
    exact h3
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  intro l _ lam w σ p hl hw hp hs
  obtain ⟨hp, hp'⟩ := hp
  obtain ⟨hs, hs'⟩ := hs
  rw [Real.rpow_zero] at hp' hs'
  have hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ := natCast_mem _ l
  have hwK : w ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← mem_algebraicClosure_iff, hw]
    exact neg_mem hlK
  have hpK : p ∈ algebraicClosure ℚ ℂ := by
    have e : p = (12 * p) / ((12 : ℕ) : ℂ) := by push_cast; ring
    rw [e]
    exact div_mem hp (natCast_mem _ 12)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (l : ℂ) = 0 := by linear_combination hw
    have h' : l = 0 := by exact_mod_cast this
    omega
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : ((l + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hw + (1 - w) * h
    exact Nat.succ_ne_zero l (by exact_mod_cast this)
  have hσK : σ ∈ algebraicClosure ℚ ℂ := by
    have e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) /
        (((2 : ℕ) : ℂ) * w * (1 + w)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]
      push_cast
      linear_combination σ * hw
    have h1 : 1 + w ∈ algebraicClosure ℚ ℂ := add_mem (one_mem _) hwK
    rw [e]
    exact div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK))
      (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)
  refine ⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩
  · have e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ) := Subtype.ext (by simpa using hw)
    rw [← map_pow, e, map_neg, map_natCast]
  · have e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩ :=
      Subtype.ext (by
        show 12 * p = ((12 : ℕ) : ℂ) * p
        norm_num)
    rw [e, map_mul, map_natCast] at hp'
    exact_mod_cast hp'
  · have e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) =
        ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e] at hs'
    simpa only [map_sub, map_mul, map_pow, map_add (f := _), map_one, map_natCast] using hs'

end GlobalTheory.SzRamified
end

section

noncomputable section

open GlobalTheory.LatVal (Sz)
open Polynomial

namespace GlobalTheory.QFam.SzRing

variable (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])

abbrev nval : Valuation ℂ_[l] NNReal := NormedField.valuation

theorem mem_integer_iff (y : ℂ_[l]) : y ∈ (nval l).integer ↔ ‖y‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
  exact Iff.rfl

def szRing : Subring ℂ :=
  ((nval l).integer.comap lam).map (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_szRing (x : ℂ) : x ∈ szRing l lam ↔ Sz l lam 0 x := by
  unfold szRing Sz
  rw [Real.rpow_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_integer_iff l _).1 hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, (mem_integer_iff l _).2 hy, rfl⟩

def toAlg : szRing l lam →+* algebraicClosure ℚ ℂ :=
  (szRing l lam).subtype.codRestrict (algebraicClosure ℚ ℂ) fun r => ((mem_szRing l lam r.1).1 r.2).1

theorem lam_toAlg_mem (r : szRing l lam) : (lam.comp (toAlg l lam)) r ∈ (nval l).integer := by
  obtain ⟨h, hr⟩ := (mem_szRing l lam r.1).1 r.2
  rw [Real.rpow_zero] at hr
  exact (mem_integer_iff l _).2 hr

theorem mem_szRing_of_isIntegral (x : ℂ) (hx : IsIntegral (szRing l lam) x) : x ∈ szRing l lam := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hc : (algebraMap (algebraicClosure ℚ ℂ) ℂ).comp (toAlg l lam) = algebraMap (szRing l lam) ℂ :=
    RingHom.ext fun _ => rfl
  have h1 : IsIntegral (algebraicClosure ℚ ℂ) x :=
    ⟨p.map (toAlg l lam), hp.map _, by rw [eval₂_map, hc, hpx]⟩
  have : Algebra.IsIntegral ℚ (algebraicClosure ℚ ℂ) :=
    ⟨fun y => (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val Subtype.val_injective).1
      (mem_algebraicClosure_iff'.1 y.2)⟩
  have h2 : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff'.2 (isIntegral_trans x h1)
  have h3 : eval₂ (toAlg l lam) ⟨x, h2⟩ p = 0 := by
    apply (algebraMap (algebraicClosure ℚ ℂ) ℂ).injective
    rw [hom_eval₂, hc, map_zero]
    exact hpx
  have h4 : eval₂ (lam.comp (toAlg l lam)) (lam ⟨x, h2⟩) p = 0 := by
    rw [← hom_eval₂, h3, map_zero]
  let g : szRing l lam →+* (nval l).integer :=
    (lam.comp (toAlg l lam)).codRestrict (nval l).integer (lam_toAlg_mem l lam)
  have hg : (algebraMap (nval l).integer ℂ_[l]).comp g = lam.comp (toAlg l lam) :=
    RingHom.ext fun _ => rfl
  have h5 : IsIntegral (nval l).integer (lam ⟨x, h2⟩) :=
    ⟨p.map g, hp.map _, by rw [eval₂_map, hg, h4]⟩
  have h6 := (Valuation.integer.integers (nval l)).mem_of_integral h5
  rw [mem_szRing]
  refine ⟨h2, ?_⟩
  rw [Real.rpow_zero]
  exact (mem_integer_iff l _).1 h6

end GlobalTheory.QFam.SzRing

theorem GlobalTheory.QFam.exists_szRing (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) :
    ∃ R : Subring ℂ, (∀ x, x ∈ R ↔ Sz l lam 0 x) ∧ ∀ x, IsIntegral R x → x ∈ R :=
  ⟨GlobalTheory.QFam.SzRing.szRing l lam, GlobalTheory.QFam.SzRing.mem_szRing l lam,
    GlobalTheory.QFam.SzRing.mem_szRing_of_isIntegral l lam⟩
end
end

section

noncomputable section

open GlobalTheory.LatVal (Sz)

namespace GlobalTheory.QFam

theorem exists_algebraic_norm_eq_rpow (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (q : ℚ) :
    ∃ x : algebraicClosure ℚ ℂ, x ≠ 0 ∧ ‖lam x‖ = (l : ℝ) ^ (-(q : ℝ)) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hlc : (l : algebraicClosure ℚ ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h1 := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p] at h1
    simpa using h1
  haveI : IsAlgClosed (algebraicClosure ℚ ℂ) := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((l : algebraicClosure ℚ ℂ) ^ q.num) q.den_pos
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow q.den_ne_zero] at hx
    exact zpow_ne_zero _ hlc hx.symm
  · have h1 : ‖lam x‖ ^ q.den = ((l : ℝ) ^ (-(q : ℝ))) ^ q.den := by
      rw [← norm_pow, ← map_pow, hx, map_zpow₀, map_natCast, norm_zpow, hl, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
        inv_zpow', ← Real.rpow_intCast]
      congr 1
      have h2 : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by exact_mod_cast q.mul_den_eq_num
      push_cast
      rw [neg_mul, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hl0.le _) q.den_ne_zero).1 h1

theorem sz_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam (-r) (x : ℂ) :=
  ⟨x.2, hx.le⟩

theorem sz_inv_of_norm_eq {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {r : ℝ} {x : algebraicClosure ℚ ℂ}
    (hx : ‖lam x‖ = (l : ℝ) ^ (-r)) : Sz l lam r (x : ℂ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨inv_mem x.2, ?_⟩
  have e : (⟨(x : ℂ)⁻¹, inv_mem x.2⟩ : algebraicClosure ℚ ℂ) = x⁻¹ := rfl
  rw [e, map_inv₀, norm_inv, hx, Real.rpow_neg hl0.le, inv_inv]

theorem exists_sz_scale : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ,
    ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  intro l _ lam q
  obtain ⟨x, hx0, hx⟩ := exists_algebraic_norm_eq_rpow l lam q
  exact ⟨x, fun h => hx0 (Subtype.ext h), sz_of_norm_eq hx, sz_inv_of_norm_eq hx⟩

end GlobalTheory.QFam
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_affine_galois_cover_dual_number_epi : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  first | (exact @GlobalTheory.DualCover.exists_dualCover) | (exact GlobalTheory.DualCover.exists_dualCover) | (intros; apply GlobalTheory.DualCover.exists_dualCover  <;> assumption)
end

section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

theorem _root_.GlobalTheory.T.exists_square_matrix_image_submodule_contains_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)), ϖ ≠ 0 → (∀ y : Fin n → O, (fun a => ϖ * y a) ∈ N) → ∃ A : Matrix (Fin n) (Fin n) O, (∀ x, x ∈ N ↔ ∃ u, A *ᵥ u = x) ∧ A.det ≠ 0 := by
  first | exact @GlobalTheory.exists_square_matrix_of_submodule_between | exact GlobalTheory.exists_square_matrix_of_submodule_between | (intros; apply GlobalTheory.exists_square_matrix_of_submodule_between <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion : ∀ (R : Type) [CommRing R] (N : ℕ) (Y : Scheme.{0}) (φ : Y ⟶ PSpace R N), IsImmersion φ → ∀ (y : Y) (V : Y.Opens) (i : Fin (N + 1)), y ∈ V → φ y ∈ GlobalTheory.ProjSpace.chart R N i → ∃ (W : Y.Opens) (hW : W ≤ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i), y ∈ W ∧ W ≤ V ∧ IsAffineOpen W ∧ ∀ g : Γ(Y, W), ∃ P Q : MvPolynomial (Fin (N + 1)) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) Q = MvPolynomial.eval₂ (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom (GlobalTheory.ProjSpace.pullRatio φ W i hW) P := by
  first | exact @GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | exact GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio | (intros; apply GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio <;> assumption)
end
