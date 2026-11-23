module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamTotalDifferentialOneFunctionPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle858
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.LatVal GlobalTheory.LatJet
open scoped nonZeroDivisors

namespace GlobalTheory.HilbertEis

theorem eisClass_summable_of_hecke (hH : HeckeWeightTwo) {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (hf : 2 ≤ Module.finrank ℚ F) (𝔞 𝔟 : Frac F) {s : ℕ} (hs : 2 ≤ s) {z : Emb F → ℂ} (hz : z ∈ upperHalf F) :
    Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := by
  obtain ⟨G, hG, -, -⟩ := hH F hf 𝔞 𝔟
  have hre : 0 < ((s : ℂ) - 1).re := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]
    exact_mod_cast (by omega : 1 < s)
  have h1 := (hG.1 ((s : ℂ) - 1) hre z hz).1
  have h2 : Summable fun c => ‖eisClass 𝔞 𝔟 2 ((s : ℂ) - 1) z c‖ := summable_norm_iff.mpr h1
  refine Summable.of_norm (h2.congr fun c => ?_)
  have hP : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero hz c.out.2.2.2 τ
  have hn : 0 < ‖∏ τ, latPt z c.out.1 τ‖ := norm_pos_iff.2 hP
  have hr : (-2 * ((s : ℂ) - 1)).re = -((2 * (s - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s)]
    simp
  simp only [eisClass, eisTerm, norm_mul, norm_pow, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hn, hr,
    mul_zero, Complex.zero_re, Real.rpow_zero, mul_one, Real.rpow_neg hn.le, Real.rpow_natCast, ← inv_pow, ← pow_add]
  congr 1
  omega

theorem dF_pos (F : Type) [Field F] [NumberField F] : 0 < dF F :=
  abs_pos.2 (by exact_mod_cast discr_ne_zero F)

theorem nrm_pos {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  unfold nrm
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem const_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (k : ℕ) :
    cK F k * (dF F * nrm 𝔞) ^ k / omegaFactor 𝔞 ^ k =
      ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ ((k : ℝ) - 1 / 2) := by
  have hd := dF_pos F
  have hn := nrm_pos 𝔞
  unfold cK omegaFactor
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (dF F ^ _), ← Real.rpow_mul hd.le, ← Real.rpow_natCast (dF F) k]
  have h1 : dF F ^ ((1 : ℝ) / 2 * k) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
  have h2 : nrm 𝔞 ^ k ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [← Real.rpow_add hd, ← Real.rpow_add hd]
  congr 1
  ring

theorem eisExp : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  intro hL hH hP F _ _ _ hf 𝔞 𝔟 s hs
  rcases Nat.lt_or_ge s 2 with h1 | h2
  · obtain rfl : s = 1 := by omega
    obtain ⟨G, hG, hd, he⟩ := hH F hf 𝔞 𝔟
    exact ⟨G 0, ⟨fun h => absurd rfl h, fun _ => ⟨G, hG, rfl⟩⟩, hd, he⟩
  have hsum : ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 (2 * s) 0 z) := fun z hz =>
    eisClass_summable_of_hecke hH hf 𝔞 𝔟 h2 hz
  refine ⟨eisSum 𝔞 𝔟 (2 * s) 0, ⟨fun _ z hz => (hsum z hz).hasSum, fun h => by omega⟩,
    GlobalTheory.T.hilbertEisensteinSeriesLattice_differentiableOn F 𝔞 𝔟 _ hsum, ?_⟩
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩
  obtain ⟨Z, Z', hZ, hZ', hfe⟩ := hP F (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) (ClassGroup.mk F 𝔞)⁻¹ D rfl
    (by rw [mul_assoc, mul_inv_cancel, mul_one])
  refine ⟨Z', hZ', fun z hz => ?_⟩
  obtain ⟨hq, h3⟩ := GlobalTheory.T.hilbertEisenstein_nonconstant_terms_hasSum F hL 𝔞 𝔟 (2 * s) (by omega) (even_two_mul s) hsum z hz
  have h0 := GlobalTheory.T.hasSum_hilbertEisenstein_constantTerm_partialZeta F 𝔞 𝔟 s (by omega) D rfl Z hZ z hz
  have hfe' := hfe ((2 * s : ℕ) : ℂ) (fun n h => by
      have h' : ((2 * s : ℕ) : ℤ) = -2 * n := by exact_mod_cast h
      omega) (fun n h => by
      have h' : (1 - ((2 * s : ℕ) : ℤ)) = -2 * n := by exact_mod_cast h
      omega)
  have hc := GlobalTheory.T.gammaReal_functionalEquation_constant_even_integer (dF F) (dF_pos F) (Module.finrank ℚ F) s (by omega) _ _ hfe'
  refine ⟨hq, ?_⟩
  have hG := (HasSum.add_compl (f := eisClass 𝔞 𝔟 (2 * s) 0 z) (s := {c : Quotient (latRel 𝔞 𝔟) | c.out.1.2 = 0}) h0 h3).tsum_eq
  rw [show eisSum 𝔞 𝔟 (2 * s) 0 z = ∑' c, eisClass 𝔞 𝔟 (2 * s) 0 z c from rfl, hG]
  have hk := const_eq F 𝔞 (2 * s)
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    unfold omegaFactor
    exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (dF_pos F) _) (nrm_pos 𝔞)).ne'
  have hcK : (cK F (2 * s) : ℂ) ≠ 0 := by
    have : 0 < cK F (2 * s) := by
      unfold cK
      exact mul_pos (pow_pos (Nat.cast_pos.2 (Nat.factorial_pos _)) _) (Real.rpow_pos_of_pos (dF_pos F) _)
    exact_mod_cast this.ne'
  have hk' : (cK F (2 * s) : ℂ) * ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) / (omegaFactor 𝔞 : ℂ) ^ (2 * s) =
      (((2 * s - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * ((dF F ^ (((2 * s : ℕ) : ℝ) - 1 / 2) : ℝ) : ℂ) := by
    exact_mod_cast hk
  rw [← hc, ← hk']
  field_simp

end GlobalTheory.HilbertEis
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMTypeRestrict

theorem exists_equiv_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := by
  intro E _ _ _ I _ φ hφ e₀
  have hreal : ∀ i, ComplexEmbedding.IsReal ((φ i).comp (algebraMap (FR E) E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  let g : Fin (Module.finrank ℚ (FR E)) → (FR E →+* ℝ) := fun j => (hreal (e₀ j)).embedding
  have hg : ∀ j (x : FR E), (g j x : ℂ) = φ (e₀ j) (x : E) := fun j x =>
    (hreal (e₀ j)).coe_embedding_apply x
  have hinj : Function.Injective g := by
    intro j k hjk
    have hc : (φ (e₀ j)).comp (algebraMap (FR E) E) = (φ (e₀ k)).comp (algebraMap (FR E) E) := by
      ext x
      have h1 := hg j x
      have h2 := hg k x
      rw [hjk] at h1
      simp only [RingHom.comp_apply]
      exact h1.symm.trans h2
    have hm : IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ j))) =
        IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ k))) := by
      rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
        InfinitePlace.comap_mk, InfinitePlace.comap_mk, hc]
    have := (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ).1 ((IsCMField.equivInfinitePlace E).injective hm)
    exact e₀.injective this
  have hcard : Fintype.card (Fin (Module.finrank ℚ (FR E))) = Fintype.card (FR E →+* ℝ) := by
    rw [Fintype.card_fin, GlobalTheory.card_realEmbeddings]
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩), fun j x => hg j x⟩

end GlobalTheory.CMTypeRestrict
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.HCF

theorem fold_replicate_cap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (c : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a) (n : ℕ) :
    (List.replicate n c).foldr (fun z f => z f - χ z • f) φ = ((c - algebraMap ℂ _ (χ c)) ^ n) φ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply]

theorem rt_translate_kill : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  intro E _ _ _ a L W X S hXS N φ hφ t κ
  obtain ⟨hA, -, -, χ₀, hχ₀, hnil⟩ := hφ
  set h := finGL E a t * infGL E a (Unitary.toUnits κ) with hh
  refine ⟨fun γ g => ?_, ?_, fun τ u => ?_⟩
  · rw [rt_apply, rt_apply, mul_assoc, hA.left]
  · refine isOpen_stab_of_mem_nhds (finRep E a) _ ?_
    have hc : Continuous fun k : GL (Fin a) (Af E) => t⁻¹ * k * t := by fun_prop
    have ho := hA.level.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_
    have hk' : rt E a (finGL E a (t⁻¹ * k * t)) φ = φ := hk
    change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    have e : finGL E a k * h = h * finGL E a (t⁻¹ * k * t) := by
      rw [hh, mul_assoc (finGL E a t), infGL_comm, ← mul_assoc (finGL E a t), ← map_mul,
        show t * (t⁻¹ * k * t) = k * t by group, map_mul]
      simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hk']
  · classical
    have hcap : cap τ u ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hc : Commute (cap (a := a) τ u) (rt E a h) := by
      have h1 : Commute (cap τ u) (rt E a (finGL E a t)) := commute_cap_finRep (a := a) τ u t
      have h2 := GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits κ)
      rw [hh, map_mul]
      exact h1.mul_right h2
    have hP : ∀ p : Polynomial ℂ, Commute (Polynomial.aeval (cap (a := a) τ u) p) (rt E a h) := by
      intro p
      have hle : Algebra.adjoin ℂ {cap (a := a) τ u} ≤ Subalgebra.centralizer ℂ {rt E a h} := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hc.eq.symm
      exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle (Polynomial.aeval_mem_adjoin_singleton ℂ _)) _ rfl).symm
    rw [← Module.End.mul_apply, (hP _).eq, Module.End.mul_apply]
    have h0 : Polynomial.aeval (cap (a := a) τ u) ((Polynomial.X - Polynomial.C (χ₀ (cap τ u))) ^ N) φ = 0 := by
      have := hnil (List.replicate N (cap τ u)) (List.length_replicate ..) fun z hz => by
        rw [List.eq_of_mem_replicate hz]; exact hcap
      rw [fold_replicate_cap] at this
      simpa [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] using this
    rw [← Finset.prod_erase_mul S _ (hXS hχ₀), Polynomial.aeval_mul, Module.End.mul_apply, h0]
    simp only [map_zero]

end GlobalTheory.HCF
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.JSW.Bialt

lemma coeff_prod_one_sub_eq_zero {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι) :
    ∀ r, s.card < r →
      PowerSeries.coeff r (∏ k ∈ s, (1 - PowerSeries.C (a k) * PowerSeries.X : PowerSeries R)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    rw [prod_empty, PowerSeries.coeff_one, if_neg (by simp at hr; omega)]
  | insert k s hk ih =>
    intro r hr
    rw [card_insert_of_notMem hk] at hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [prod_insert hk, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, ih _ (by omega), ih _ (by omega), mul_zero, sub_zero]

def ec (n : ℕ) (i : Fin n) (r : ℕ) : MvPolynomial (Fin n) ℤ :=
  PowerSeries.coeff r (∏ k ∈ univ.erase i,
    (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X))

lemma ec_eq_zero {n : ℕ} (i : Fin n) {r : ℕ} (hr : n ≤ r) : ec n i r = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have := i.2
  omega

lemma sum_ec_hsymm {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range (a + 1), ec n i r * MvPolynomial.hsymm (Fin n) ℤ (a - r) = MvPolynomial.X i ^ a := by
  have hAB : (∏ k ∈ univ.erase i,
      (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X)) *
      (∏ j : Fin n, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial (Fin n) ℤ) ^ m)) =
      PowerSeries.mk (fun m => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m) := by
    rw [← prod_erase_mul _ _ (mem_univ i), ← mul_assoc, ← prod_mul_distrib,
      prod_eq_one fun j _ => Formalism.FT.SymmetricSeries.geom_mul _, one_mul]
  have h := congrArg (PowerSeries.coeff a) hAB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Formalism.FT.SymmetricSeries.coeff_prod_geom, ec] using h

lemma sum_ec_hsymm' {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      MvPolynomial.X i ^ a := by
  rw [← sum_ec_hsymm i a]
  have h1 : ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [ec_eq_zero i (by simpa using hr), zero_mul]
  have h2 : ∑ r ∈ range (a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [if_pos (by simp at hr; omega), mul_zero]
  rw [h1, ← h2]
  refine sum_congr rfl fun r hr => ?_
  rw [if_neg (by simp at hr; omega)]

lemma pow_matrix_eq (n : ℕ) (α : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (α j)) =
      (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) *
        (Matrix.of fun m j : Fin n => if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.of_apply, ← sum_ec_hsymm' i (α j), ← sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun m => ec n i (n - 1 - m) * (if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))))]
  rfl

lemma det_pow_matrix (n : ℕ) (l : Fin n → ℕ) :
    Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) * schur n l := by
  rw [pow_matrix_eq n (fun j => l j + n - 1 - (j : ℕ)), Matrix.det_mul, schur, ← Matrix.det_transpose (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))]
  congr 2
  refine Matrix.ext fun m j => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hm := m.2
  have hj := j.2
  by_cases h : ((l j : ℤ) - j + m) < 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    congr 1
    omega

lemma schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · refine prod_eq_one fun i _ => ?_
    simp [MvPolynomial.hsymm_zero]
  · intro i j hij
    have : (j : ℕ) < i := hij
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

end GlobalTheory.JSW.Bialt

namespace GlobalTheory.JSW

theorem schur_mul_det_eq_det (n : ℕ) (l : Fin n → ℕ) (_hl : Antitone l) :
    schur n l * Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  have h0 := Bialt.det_pow_matrix n (fun _ => 0)
  simp only [zero_add, Bialt.schur_zero, mul_one] at h0
  rw [h0, Bialt.det_pow_matrix n l, mul_comm]

end GlobalTheory.JSW
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TotTwoBaseChange

section Pi

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} {M M' : J → Type}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)]

def piSL (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := funext fun i ↦ map_add (f i) (x i) (y i)
  map_smul' r x := funext fun i ↦ map_smulₛₗ (f i) r (x i)

theorem piSL_bijective [Finite J] {f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i}
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f (piSL f) (fun _ _ ↦ rfl) hf

end Pi

section Prod

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M N M' N' : Type}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']

def prodSL (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N') :
    (M × N) →ₛₗ[algebraMap R R'] (M' × N') where
  toFun x := (f x.1, g x.2)
  map_add' x y := Prod.ext (map_add f x.1 y.1) (map_add g x.2 y.2)
  map_smul' r x := Prod.ext (map_smulₛₗ f r x.1) (map_smulₛₗ g r x.2)

theorem prodSL_bijective {f : M →ₛₗ[algebraMap R R'] M'} {g : N →ₛₗ[algebraMap R R'] N'}
    (hf : Function.Bijective (liftSemi f)) (hg : Function.Bijective (liftSemi g)) :
    Function.Bijective (liftSemi (prodSL f g)) :=
  liftSemi_prod_bijective R R' M N M' N' f g (prodSL f g) (fun _ ↦ rfl) hf hg

end Prod

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs H
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add _, map_smul' := hs T }
  have h : ∀ T : C, SemiHom (algebraMap R R') (α T) := hs
  have h0 : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ H T (a T) fun _ ↦ rfl
  have h1 : ∀ T, Function.Bijective (liftSemi (h T).m1) := fun T ↦
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T)
  have h2 : ∀ T, Function.Bijective (liftSemi ((h T).mOm 2)) := fun T ↦
    GlobalTheory.FormsBaseChange.bijective_liftSemi_mOm R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T) (h1 T) 2
  have k2 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦ piSL_bijective fun T'' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ piSL_bijective fun _ : T' ⟶ T'' ↦ h0 T''
  have k1 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ h1 T'
  have k0 := piSL_bijective h2
  have k := prodSL_bijective k1 k0
  refine liftSemi_prod_bijective R R' (C2 F) (A1 F × W0 F 2) (C2 F') (A1 F' × W0 F' 2) _ _ _ ?_ k2 k
  intro x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ; exact cechDeRhamPullbackTotalDegreeTwo_function_part _ φ ψ x
  · funext T T' φ; exact pullTot2_a _ φ x
  · funext T; exact pullTot2_η _ x T

end GlobalTheory.TotTwoBaseChange
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem totalZeroCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ C _ _ _ F F' α _ hs hb g hg
  let f : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T =>
    { toFun := α T
      map_add' := fun a b => map_add (α T) a b
      map_smul' := fun r b => hs T r b }
  exact liftSemi_pi_bijective R R' C (fun T => F.obj T) (fun T => F'.obj T) f g
    (fun x T => hg x T) (fun T => hb T (f T) (fun _ => rfl))

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  first | exact @GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | exact GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | (intros; apply GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isNil_dual_frobenius_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → GlobalTheory.PDivLat.IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  first | exact @GlobalTheory.DualFrobNil.isNil_dual_frobenius | exact GlobalTheory.DualFrobNil.isNil_dual_frobenius | (intros; apply GlobalTheory.DualFrobNil.isNil_dual_frobenius <;> assumption)
end
