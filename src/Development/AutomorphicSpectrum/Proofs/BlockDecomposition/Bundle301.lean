module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import GroundTheory.AutomorphicForms.MacdonaldHecke
import GroundTheory.AutomorphicForms.MacdonaldRecursion
public import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle293
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle294
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PDUniv

theorem pdPoly_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  intro B _ J δ C _ J'' δ'' f hf x hx
  have hη : (pq B).IsStd δ (eta δ) := by
    unfold eta
    exact Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))
  letI : Algebra B C := f.toAlgebra
  let L : (pq B).P →ₗ[B] C := (pq B).e.constr ℕ fun n => δ''.dpow n x
  have hL : ∀ n, L ((pq B).e n) = δ''.dpow n x := fun n => (pq B).e.constr_basis ℕ _ n
  have h1 : L 1 = 1 := by
    rw [← (pq B).e_zero, hL, δ''.dpow_zero hx]
  have hbil : (LinearMap.mul B (pq B).P).compr₂ L = (LinearMap.mul B C).compl₁₂ L L := by
    refine (pq B).e.ext fun m => (pq B).e.ext fun n => ?_
    show L ((pq B).e m * (pq B).e n) = L ((pq B).e m) * L ((pq B).e n)
    rw [(pq B).e_mul, ← nsmul_eq_mul, map_nsmul]
    simp only [hL]
    rw [nsmul_eq_mul, δ''.mul_dpow hx]
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => LinearMap.congr_fun₂ hbil a b
  let F : (pq B).P →+* C := (AlgHom.ofLinearMap L h1 hmul).toRingHom
  have hFL : ∀ p, F p = L p := fun p => rfl
  have hFe : ∀ n, F ((pq B).e n) = δ''.dpow n x := fun n => (hFL _).trans (hL n)
  have hFa : ∀ b, F (algebraMap B (pq B).P b) = f b := fun b =>
    (AlgHom.ofLinearMap L h1 hmul).commutes b
  have hcomp : F.comp (algebraMap B (pq B).P) = f := RingHom.ext hFa
  have he1 : F ((pq B).e 1) = x := by rw [hFe, δ''.dpow_one hx]
  have he1mem : (pq B).e 1 ∈ (pq B).ext J := by
    unfold PDPoly.ext PDPoly.aug
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  have hSspan : (pq B).ext J = Ideal.span ((algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1)) := by
    rw [Ideal.span_union]
    rfl
  have hS' : ∀ s ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1),
      F s ∈ J'' := by
    rintro s (⟨j, hj, rfl⟩ | ⟨n, rfl⟩)
    · rw [hFa]
      exact hf.ideal_comp (Ideal.mem_map_of_mem f hj)
    · rw [hFe]
      exact δ''.dpow_mem (Nat.succ_ne_zero n) hx
  have hdpS : ∀ {n : ℕ}, ∀ a ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1), F ((eta δ).dpow n a) = δ''.dpow n (F a) := by
    intro n a ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨m, rfl⟩
    · rw [hη.dp.dpow_comp j hj, hFa, hFa, hf.dpow_comp j hj]
    · dsimp only
      have hv : (pq B).e (m + 1) = (eta δ).dpow (m + 1) ((pq B).e 1) := (hη.var (m + 1)).symm
      rw [hv, (eta δ).dpow_comp (Nat.succ_ne_zero m) he1mem]
      simp only [hη.var, map_mul, map_natCast, hFe]
      rw [δ''.dpow_comp (Nat.succ_ne_zero m) hx]
  have hdp : IsDPMorphism (eta δ) δ'' F := IsDPMorphism.on_span (eta δ) δ'' hSspan hS' hdpS
  refine ⟨F, ⟨hcomp, he1, hdp⟩, ?_⟩
  rintro G ⟨hG1, hG2, hG3⟩
  have hGa : ∀ b, G (algebraMap B (pq B).P b) = f b := fun b => RingHom.congr_fun hG1 b
  have hGe : ∀ n, G ((pq B).e n) = δ''.dpow n x := by
    intro n
    rw [← hη.var n, ← hG3.dpow_comp _ he1mem, hG2]
  let Ga : (pq B).P →ₐ[B] C := { G with commutes' := hGa }
  have hlin : Ga.toLinearMap = L := (pq B).e.ext fun n => by
    show G ((pq B).e n) = L ((pq B).e n)
    rw [hGe, hL]
  ext p
  exact LinearMap.congr_fun hlin p

end GlobalTheory.CompanionTheory.PDUniv
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SitePD

theorem pdPoly_flat_comp : ∀ {A B : Type} [CommRing A] [CommRing B] (i : A →+* B), i.Flat →
    ((algebraMap B (pq B).P).comp i).Flat := by
  intro A B _ _ i hi
  have hfree : Module.Free B (pq B).P := Module.Free.of_basis (pq B).e
  have h2 : (algebraMap B (pq B).P).Flat := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  exact RingHom.Flat.comp hi h2

end GlobalTheory.CompanionTheory.SitePD
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDCrit

private theorem pq_isStd_eta {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    (pq B).IsStd δ (eta δ) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem repr_sum {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  have hs := pq_isStd_eta δ
  have h1 : (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hs.var k, Algebra.smul_def]
  rw [h1, (pq B).e.repr_linearCombination]

theorem mem_span_iff {B : Type} [CommRing B] (c : B) (z : (pq B).P) :
    z ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, (pq B).e.repr z k ∈ Ideal.span {c} := by
  constructor
  · intro hz k
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  · intro h
    choose d hd using fun k => Ideal.mem_span_singleton'.1 (h k)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ k ∈ ((pq B).e.repr z).support, d k • (pq B).e k, ?_⟩
    conv_rhs => rw [← (pq B).e.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hd k, mul_comm (d k • (pq B).e k), ← Algebra.smul_def, smul_smul, mul_comm c (d k)]

private theorem sum_finsupp_single_apply_eq_ite {B : Type} [CommRing B] (s : Finset ℕ) (a : ℕ → B) (k : ℕ) :
    (∑ i ∈ s, Finsupp.single i (a i)) k = if k ∈ s then a k else 0 := by
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mem_fil_sup_iff {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r : ℕ) (c : B)
    (z : (pq B).P) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  constructor
  · intro hz k
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact Submodule.add_mem_sup ((hT r a).1 ha k) ((mem_span_iff c s).1 hs k)
  · intro h
    choose a ha s hs hsum using fun k => Submodule.mem_sup.1 (h k)
    have hF : (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) = (pq B).e.repr z := by
      ext k
      rw [Finsupp.add_apply, sum_finsupp_single_apply_eq_ite, sum_finsupp_single_apply_eq_ite]
      split_ifs with hk
      · exact hsum k
      · rw [add_zero]
        exact (Finsupp.notMem_support_iff.1 hk).symm
    have hz : z = (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) := by
      rw [← map_add (f := _), hF, LinearEquiv.symm_apply_apply]
    rw [hz]
    refine Submodule.add_mem_sup ((hT r _).2 fun k => ?_) ((mem_span_iff c _).2 fun k => ?_)
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact ha k
      · exact Submodule.zero_mem _
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact hs k
      · exact Submodule.zero_mem _

theorem coeff_criteria : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) (r : ℕ) (c : B), ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = 0 ↔ ∀ k, b k = 0) := by
  intro B _ J δ b r c
  have hT := (GlobalTheory.T.divided_power_polynomial_filtration δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  have hr := repr_sum δ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT, hr]
  · rw [mem_fil_sup_iff, hr]
  · rw [mem_span_iff, hr]
  · rw [← LinearEquiv.map_eq_zero_iff (pq B).e.repr, hr]
    simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

end GlobalTheory.CompanionTheory.PDCrit
end

section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {n : ℕ}

theorem prod_varL_eq_monomial (S : Finset (Fin n)) :
    ∏ k ∈ S, varL k = monomial (lamS S) := by
  have h : lamS S = ∑ k ∈ S, (Pi.single k 1 : Fin n → ℤ) := by
    funext x
    simp [lamS_apply, Finset.sum_apply, Pi.single_apply]
  rw [h]
  simp only [varL, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

theorem sum_esymmL_mul_pow (i : Fin n) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r * varL i ^ (n - r) = 0 := by
  have h0 : ∏ k : Fin n, (-varL k + varL i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Finset.prod_add, Finset.sum_powerset] at h0
  rw [← h0, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [esymmL, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [Finset.prod_neg, hc, prod_varL_eq_monomial, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, hc]

theorem altQuot_zero' : altQuot (0 : LaurentRing n) = 0 :=
  altQuot_eq_of_mul (by simp)

theorem sum_esymmL_mul_schur (hn : 0 < n) (j : ℤ) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) (j - (r : ℤ))) = 0 := by
  set i₀ : Fin n := ⟨0, hn⟩
  set P : LaurentRing n := monomial (Pi.single i₀ (j - (n : ℤ)) + staircase n) with hP
  have hterm : ∀ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single i₀ (j - (r : ℤ))) =
      altQuot ((-1) ^ r * esymmL n r * varL i₀ ^ (n - r) * P) := by
    intro r hr
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hsym : ∀ σ, permAct σ ((-1) ^ r * esymmL n r) = (-1) ^ r * esymmL n r := by
      intro σ
      rw [map_mul, map_pow, map_neg, map_one, permAct_esymmL]
    rw [mul_assoc ((-1) ^ r * esymmL n r), altQuot_mul_of_symm hsym, schur]
    congr 2
    rw [← monomial_single_natCast, hP, ← monomial_add, ← add_assoc, ← Pi.single_add]
    congr 3
    push_cast [Nat.cast_sub hr']
    ring
  rw [Finset.sum_congr rfl hterm, ← altQuot_sum, ← Finset.sum_mul, sum_esymmL_mul_pow, zero_mul,
    altQuot_zero']

theorem schur_single_eq_zero (hn : 0 < n) {m : ℤ} (h1 : 1 - (n : ℤ) ≤ m) (h2 : m ≤ -1) :
    schur (Pi.single (⟨0, hn⟩ : Fin n) m) = 0 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_zero]
  have hlt : (-m).toNat < n := by omega
  refine (alternant_eq_zero (i := (⟨0, hn⟩ : Fin n)) (j := ⟨(-m).toNat, hlt⟩) ?_ ?_).symm
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · have hne : (⟨(-m).toNat, hlt⟩ : Fin n) ≠ ⟨0, hn⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, staircase]
    have : (((-m).toNat : ℕ) : ℤ) = -m := by omega
    simp only [this]
    ring

theorem schur_zero_eq_one : schur (0 : Fin n → ℤ) = 1 :=
  altQuot_eq_of_mul (by rw [mul_one, zero_add]; rfl)

theorem sum_range_esymmL_mul_schur (hn : 0 < n) {j : ℕ} (hj : 1 ≤ j) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) ((j - r : ℕ) : ℤ)) = 0 := by
  set f : ℕ → LaurentRing n := fun r => (-1) ^ r * esymmL n r *
    schur (Pi.single (⟨0, hn⟩ : Fin n) ((j : ℤ) - (r : ℤ))) with hf
  have h1 : ∑ r ∈ Finset.range (j + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hjr : j < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    by_cases hrn : n < r
    · simp only [hf]
      rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
    · simp only [hf]
      rw [schur_single_eq_zero hn (by omega) (by omega), mul_zero]
  have h2 : ∑ r ∈ Finset.range (n + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hrn : n < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    simp only [hf]
    rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
  have h3 : ∑ r ∈ Finset.range (j + 1), f r = 0 := by
    rw [h1, ← h2]
    exact sum_esymmL_mul_schur hn (j : ℤ)
  rw [← h3]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  simp only [hf]
  rw [Nat.cast_sub hr']

theorem monomialChar_lamS (S : Finset (Fin n)) (z : Fin n → ℂˣ) :
    monomialChar (lamS S) z = ∏ i ∈ S, (z i : ℂ) := by
  rw [monomialChar_apply]
  have h : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1 := by
    intro i
    rw [lamS_apply]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem schur_row_recursion : L8 := by
  intro n hn z
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 : (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ) : Fin n → ℤ) = 0 := by
      simp
    rw [h0, schur_zero_eq_one, map_one]
  · have h := congrArg (evalAt z) (sum_range_esymmL_mul_schur hn hj)

    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, evalAt_esymmL,
    monomialChar_lamS] at h
    exact h

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.KOneFactor

open GlobalTheory.LocGL GlobalTheory.LocGL.IwahoriFactor

theorem sub_one_apply_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n)
    {c : GL (Fin n) k} (hc : c ∈ unipRadLower k e) (i j : Fin n)
    (hij : ¬ (e.symm j).1 < (e.symm i).1) : ((c : Matrix (Fin n) (Fin n) k) - 1) i j = 0 := by
  obtain ⟨hP, hD⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).1 hc
  have hB := (GlobalTheory.SmGL.mem_parabLower_iff k).1 hP
  obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
  simp only [Equiv.symm_apply_apply] at hij
  rw [Matrix.sub_apply, sub_eq_zero]
  rcases (not_lt.1 hij).lt_or_eq with hab | rfl
  · rw [hB a b p q hab, GlobalTheory.LocGL.IwahoriFactor.one_ne e hab.ne p q]
  · rw [hD a p q, GlobalTheory.LocGL.IwahoriFactor.one_same e a p q]

theorem kone_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ KOne k (Fin n),
    ∃ m : Levi k (fun a => Fin (d a)), leviEmb k e m ∈ KOne k (Fin n) ∧
      ∃ x ∈ unipRad k e ⊓ KOne k (Fin n), ∃ c ∈ lowC k e, g = leviEmb k e m * x * c := by
  intro k _ _ _ _ n s d e g hg
  obtain ⟨c, hc, hgc⟩ := GlobalTheory.LocGL.IwahoriFactor.exists_mul_mem_parab e hg
  have hcP : c ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
    first
    | exact hc.2
  have hcl : c⁻¹ ∈ GlobalTheory.SmGL.unipRadLower k e := by
    have hci := inv_mem hc
    first
    | exact hci.1
  obtain ⟨u, hu, hpu⟩ := GlobalTheory.SmGL.exists_levi_mul_unip k e ⟨g * c, hgc⟩
  let m := GlobalTheory.SmGL.leviProj k e ⟨g * c, hgc⟩
  have hpP : leviEmb k e m ∈ KOne k (Fin n) := by
    apply StepData.mem_KOne.2
    intro i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst b
      have h := StepData.mem_KOne.1 (mul_mem hg hcP) (e ⟨a, i⟩) (e ⟨a, j⟩)
      rw [Matrix.sub_apply, one_same] at h
      simpa [Matrix.sub_apply, one_same, m] using h
    · rw [Matrix.sub_apply, GlobalTheory.SmGL.leviEmb_apply_ne k e m hab, one_ne e hab, sub_zero, map_zero]
      exact zero_lt_one
  refine ⟨m, hpP, u, ?_, c⁻¹, ?_, eq_mul_inv_of_mul_eq hpu⟩
  · have hug : (GlobalTheory.SmGL.leviEmb k e m)⁻¹ * (g * c) = u := inv_mul_eq_iff_eq_mul.2 hpu
    have huP : u ∈ GlobalTheory.SplitWeil.KOne k (Fin n) := by
      rw [← hug]
      exact mul_mem (inv_mem hpP) (mul_mem hg hcP)
    have hur : u ∈ GlobalTheory.SmGL.unipRad k e := by
      first
      | exact hu
    exact Subgroup.mem_inf.2 ⟨hur, huP⟩
  · show _ ∧ _
    exact ⟨inv_mem hcP, fun i j hij => GlobalTheory.CompanionTheory.KOneFactor.sub_one_apply_eq_zero e hcl i j hij⟩

end GlobalTheory.CompanionTheory.KOneFactor
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.modulus_contracting_block_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | exact GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | (intros; apply GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.last_block_central_scalar_modulus_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), j.val + 1 = h → leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = Matrix.GeneralLinearGroup.scalar (Fin N) t ∧ modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) = 1 := by
  intro k _ _ _ _ h N d hd t j hj
  open GlobalTheory.CompanionTheory.ZjScalar in
    constructor
    · apply Units.ext
      ext p q
      obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective p
      obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective q
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, zj_last d t j hj a]
        by_cases hxy : x = y
        · subst hxy
          simp [Matrix.GeneralLinearGroup.scalar]
        · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by simpa using (stdBlocks d hd).injective e)
          simp [Matrix.GeneralLinearGroup.scalar, hxy, this]
      · have : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e =>
          hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))
        rw [leviEmb_apply_ne k _ _ hab]
        simp [Matrix.GeneralLinearGroup.scalar, this]
    · have hx : nabs k t ≠ 0 := (nabs_pos' k t).ne'
      simp only [modulus, nabs_det_zj_last d t j hj]
      have : ∀ a, (nabs k t ^ d a) ^ modExp (fun a => Fin (d a)) a =
          nabs k t ^ ((d a : ℤ) * modExp (fun a => Fin (d a)) a) := fun a => by
        rw [zpow_mul, zpow_natCast]
      simp only [this]
      rw [prod_zpow_eq _ _ hx, sum_card_mul_modExp, zpow_zero]
end
