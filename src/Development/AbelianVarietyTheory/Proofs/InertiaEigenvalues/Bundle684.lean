module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle603
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle654
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle653
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle656
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle648
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle587
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle661
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle585
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EnvExist

variable {l : ℕ}

theorem iter_map {A B : Type} [CommRing A] [CommRing B] {D : Delta l A} {D' : Delta l B} {g : A →+* B}
    (hg : IsδMap D D' g) (n : ℕ) (x : A) : g (D.δ^[n] x) = D'.δ^[n] (g x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

theorem polyEval_isδ [Fact l.Prime] {A C : Type} [CommRing A] [CommRing C] (D : Delta l A) (DC : Delta l C)
    (f : A →+* C) (hf : IsδMap D DC f) (v : C) :
    IsδMap (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
  intro x
  have : x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
    refine MvPolynomial.induction_on x ?_ ?_ ?_
    · intro a
      rw [mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact hf a
    · intro p q hp hq
      exact add_mem hp hq
    · intro p k hp
      refine mul_mem hp ?_
      rw [mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Function.iterate_succ_apply']
  exact mem_δLocus.1 this

end GlobalTheory.BSP.EnvExist


open GlobalTheory.BSP.EnvExist in
theorem GlobalTheory.BSP.envRing_exists : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A →
    Nonempty (EnvRing D J d p) := by
  intro l _ A _ D J d p hfg hl hd hδ hc
  have hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p)) := by
    rintro _ ⟨k, rfl⟩
    refine Ideal.subset_span ⟨k + 1, ?_⟩
    unfold envRel
    exact Function.iterate_succ_apply' _ _ _
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_quotient_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk
  set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs
  obtain ⟨Q, _, iQ, hQ⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ (J.map s) (hfg.map s)
  have hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s := by
    rw [← map_natCast s]; exact Ideal.mem_map_of_mem s hl
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q iQ (J.map s) hQ hlL DL
  have hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']

  have hshape := GlobalTheory.T.prismaticEnvelopeRelation_triangular l A D J d p hl hd hδ
  have hlev := GlobalTheory.T.digitMonomials_basis_envelope_mod_pow l A J (envRel D d p) hshape
  have hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1) := by
    intro α a
    rw [hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) =
      c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1) := fun c => by
    rw [map_finsuppSum]; exact Finsupp.sum_congr fun α _ => hmono α.1 (c α)
  have hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) →
      mk y ∈ (J ^ n).map s := by
    intro n y hy
    have h := Ideal.mem_map_of_mem mk hy
    rwa [Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at h
  have hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s →
      y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    intro n y hy
    rw [hs, ← Ideal.map_map] at hy
    have h := Ideal.mem_comap.2 hy
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm] at h
  obtain ⟨tb, htb⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l)
    (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩
    (by simp) hc hQ
    (fun n x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc'⟩ := (hlev n).1 y
      refine ⟨c, ?_⟩
      have h := hmapmem n _ hc'
      rwa [map_sub, hsum] at h)
    (fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))
  have hiδ : IsδMap D DQ (iQ.comp s) := by
    intro a
    show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))
    rw [← polyDelta_C, hDL, hDQ]
  set_option synthInstance.maxHeartbeats 200000 in
  have hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0 := by
    show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0
    have h0 : mk (envRel D d p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
    rw [← map_mul iQ, ← map_mul mk, ← map_add iQ, ← map_add mk, ← hDQ, ← hDL]
    change iQ (mk (envRel D d p 0)) = 0
    rw [h0, map_zero]
  have htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n := by
    intro α
    rw [htb α]
    show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    refine Finsupp.prod_congr fun k _ => ?_
    rw [map_pow, RingHom.comp_apply, hX]
  have hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
      IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
      ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v := by
    intro C _ DC JC hC f hf hJ v hv
    have hg₀ := polyEval_isδ D DC f hf v
    set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def
    have hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v := by
        simp [g₀]
      show g₀ (envRel D d p k) = 0
      rw [envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]
      exact Function.iterate_fixed DC.δ_zero k
    set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def
    have hg₁C : g₁.comp s = f := RingHom.ext fun a => by
      show g₀ (MvPolynomial.C a) = f a
      exact MvPolynomial.eval₂Hom_C _ _ _
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)
    have e : ∀ z, h (iQ z) = g₁ z := fun z => RingHom.congr_fun hh z
    have hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ := by
      rw [← map_natCast iQ]; exact Ideal.mem_map_of_mem iQ hlL
    have hJQ : ((J.map s).map iQ).map h ≤ JC := by
      rw [Ideal.map_map, hh, Ideal.map_map, hg₁C]; exact hJ
    have hhδ : IsδMap DQ DC h := GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance
      (fun x n => by
        obtain ⟨b, hb⟩ := hQ.surj x n
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨iQ (mk y), ?_, ?_⟩
        · rw [mem_δLocus, ← hDQ, ← hDL, e, e]
          exact hg₀ y
        · rw [← Ideal.map_pow]; exact hb)
    refine ⟨h, hhδ, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, hh, hg₁C]
    · show h (iQ (mk (MvPolynomial.X 0))) = v
      rw [e]
      show g₀ (MvPolynomial.X 0) = v
      rw [hg₀def, MvPolynomial.eval₂Hom_X']
      rfl
  exact ⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩
end
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem _root_.GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  first | exact @GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | exact GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | (intros; apply GlobalTheory.SerSys.ParVec.has_mul_of_isParVec <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalDecomp

theorem galQ_eq_GK_mul_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k := by
  intro l _ a e _ _ ϖ hea g
  have hl := (Fact.out : l.Prime)
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by omega⟩
  have hG := ϖ.isGalois_field a hdvd
  have hK : FiniteDimensional ℚ_[l] (ϖ.field a).1 := (ϖ.field a).2
  have hcop : Nat.Coprime l e := by
    refine (Nat.Prime.coprime_iff_not_dvd hl).2 fun h => ?_
    have h2 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← hea] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
  have hbot : (ϖ.field a).1 ⊓ ϖ.Kinf = ⊥ := by
    set F := (ϖ.field a).1 ⊓ ϖ.Kinf with hF
    haveI : FiniteDimensional ℚ_[l] F := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toLinearMap (IntermediateField.inclusion (inf_le_left : F ≤ (ϖ.field a).1)).toRingHom.injective
    obtain ⟨n, hn⟩ := GlobalTheory.T.le_adjoin_compatibleRoots_of_finite_kummerTower l e ϖ F inferInstance inf_le_right
    have hN : 0 < l ^ n := pow_pos hl.pos n
    have hx : (ϖ.seq n ^ e) ^ (l ^ n) = -(l : Om l) := by rw [← pow_mul, mul_comm]; exact ϖ.seq_pow_mul n
    have hx0 : ϖ.seq n ^ e ≠ 0 := pow_ne_zero _ (ϖ.seq_ne_zero n)
    have hint : IsIntegral F (ϖ.seq n ^ e) := (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) (ϖ.seq n ^ e)).tower_top
    have hc0 : (minpoly F (ϖ.seq n ^ e)).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
    have hcF : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ∈ F := ((minpoly F (ϖ.seq n ^ e)).coeff 0).2
    have hc : (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) ≠ 0 := by
      simpa using hc0
    obtain ⟨j, hj⟩ := GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow l a e ϖ _ (IntermediateField.mem_inf.1 hcF).1 hc
    have h2 := GlobalTheory.T.norm_minpoly_coeff_zero_pow_of_pow_eq_neg_prime l F (l ^ n) (ϖ.seq n ^ e) hN hx
    have h4 := GlobalTheory.T.finrank_mul_natDegree_minpoly_le_of_pow_eq_neg l F (l ^ n) (ϖ.seq n ^ e) hN hx hn
    have hm : 0 < (minpoly F (ϖ.seq n ^ e)).natDegree := minpoly.natDegree_pos hint
    set m := (minpoly F (ϖ.seq n ^ e)).natDegree with hmdef
    set c : Om l := (((minpoly F (ϖ.seq n ^ e)).coeff 0 : F) : Om l) with hcdef
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
    have hl1 : (l : ℝ) ≠ 1 := by exact_mod_cast hl.one_lt.ne'
    have key : (l : ℝ) ^ (j * ((l ^ n : ℕ) : ℤ)) = (l : ℝ) ^ (-((m * e : ℕ) : ℤ)) := by
      have e1 : ‖c‖ ^ (e * l ^ n) = ((l : ℝ) ^ j) ^ (l ^ n) := by rw [pow_mul, hj]
      have e2 : ‖c‖ ^ (e * l ^ n) = (((l : ℝ)⁻¹) ^ m) ^ e := by rw [mul_comm, pow_mul, h2]
      rw [_root_.zpow_mul, zpow_natCast, ← e1, e2, _root_.zpow_neg, zpow_natCast, ← pow_mul, inv_pow]
    have key2 : j * ((l ^ n : ℕ) : ℤ) = -((m * e : ℕ) : ℤ) := zpow_right_injective₀ hl0 hl1 key
    have hdv : l ^ n ∣ m * e := by
      have : ((l ^ n : ℕ) : ℤ) ∣ ((m * e : ℕ) : ℤ) := ⟨-j, by linarith⟩
      exact Int.natCast_dvd_natCast.1 this
    have hdm : l ^ n ∣ m := (Nat.Coprime.pow_left n hcop).dvd_of_dvd_mul_right hdv
    have hle : l ^ n ≤ m := Nat.le_of_dvd hm hdm
    have hfr : Module.finrank ℚ_[l] F = 1 := by
      have hpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
      by_contra hne
      have : 2 * m ≤ Module.finrank ℚ_[l] F * m := Nat.mul_le_mul_right _ (by omega)
      omega
    exact IntermediateField.finrank_eq_one_iff.1 hfr
  exact GlobalTheory.T.exists_mul_fixingSubgroup_of_inf_eq_bot l (ϖ.field a).1 ϖ.Kinf hK hG hbot g

end GlobalTheory.NgalDecomp
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinPrism_galoisLift_isPrismHom : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  first | exact @GlobalTheory.BKGal.PrismTwist.hom_restrict | exact GlobalTheory.BKGal.PrismTwist.hom_restrict | (intros; apply GlobalTheory.BKGal.PrismTwist.hom_restrict <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  first | exact @GlobalTheory.FrobCong.sigma_eq_pow_add | exact GlobalTheory.FrobCong.sigma_eq_pow_add | (intros; apply GlobalTheory.FrobCong.sigma_eq_pow_add <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.KunrDisj

theorem mem_Kunr_of_mem_Kur_of_mem_sup : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l →
    x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  intro l _ a e _ _ ϖ n x hxK hx
  have hN : 0 < l ^ n * e :=
    Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))
  have hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := ϖ.seq_pow_mul n
  set U := Kunr l a with hU
  set π := ϖ.seq n with hπdef

  have hdeg := fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) =>
    GlobalTheory.T.natDegree_minpoly_root_neg_prime_unramified l (l ^ n * e) π hN hπ E h
  have hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) →
      IsIntegral E π := by
    intro E _ _ h
    by_contra hni
    have := hdeg E h
    rw [minpoly.eq_zero hni, Polynomial.natDegree_zero] at this
    omega
  let K2 : IntermediateField U (Om l) := IntermediateField.adjoin U {π}
  have hxK2 : x ∈ K2 := by
    have : x ∈ K2.restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact hx
    exact this
  let K1 : IntermediateField U (Om l) := IntermediateField.adjoin U {x}
  have hK1K2 : K1 ≤ K2 := IntermediateField.adjoin_simple_le_iff.2 hxK2
  have hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l := fun y => Kunr_le_Kur l a y.2
  have hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l := by
    intro y
    have hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l] := y.2
    rw [IntermediateField.restrictScalars_adjoin] at hy
    refine (IntermediateField.adjoin_le_iff.2 ?_) hy
    rintro z (hz | hz)
    · exact Kunr_le_Kur l a hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hxK

  let L : IntermediateField K1 (Om l) := IntermediateField.adjoin K1 {π}
  have hLK2 : L.restrictScalars U = K2 := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · exact hK1K2 hz
    · rw [Set.mem_singleton_iff.1 hz]; exact IntermediateField.mem_adjoin_simple_self U π
  have hK2r : Module.finrank U K2 = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint U hUK)]; exact hdeg U hUK
  have hLr : Module.finrank K1 L = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint K1 hK1K)]; exact hdeg K1 hK1K
  have hLU : Module.finrank U L = l ^ n * e := by
    rw [← hK2r, ← hLK2]; rfl
  have htower := Module.finrank_mul_finrank U K1 L
  rw [hLr, hLU] at htower
  have h1 : Module.finrank U K1 = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)
    exact this
  have hbot : K1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  have : x ∈ K1 := IntermediateField.mem_adjoin_simple_self U x
  rw [hbot, IntermediateField.mem_bot] at this
  obtain ⟨y, rfl⟩ := this
  exact y.2

end GlobalTheory.KunrDisj
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_frobeniusMatrix_crystallineModule_over_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), C.InvB → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∃ (c₁ c₃ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
  first | exact @GlobalTheory.SeedF.frob_matrix | exact GlobalTheory.SeedF.frob_matrix | (intros; apply GlobalTheory.SeedF.frob_matrix <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMaps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F) ∧ (∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F) ∧ 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  intro l _ K bk
  exact ⟨GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l, (GlobalTheory.T.galois_action_extends_to_ainf_disc_rings l K bk).2, GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom l K bk,
    (GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk).2.2.1⟩

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) → ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  first | exact @GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | exact GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree | (intros; apply GlobalTheory.BSP.exists_galK_fixFlat_of_tilt_maps_agree <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisin_approxRoot_image_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  first | exact @GlobalTheory.BSP.approx_root_indep | exact GlobalTheory.BSP.approx_root_indep | (intros; apply GlobalTheory.BSP.approx_root_indep <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_galois_conj_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  first | exact @GlobalTheory.BSP.exists_gal_of_teichmuller_congr | exact GlobalTheory.BSP.exists_gal_of_teichmuller_congr | (intros; apply GlobalTheory.BSP.exists_gal_of_teichmuller_congr <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ‖toDisc l (BK.hf f X) bk.ρ₀ (BK.hf g X)‖ ≤ bk.ρ₀ ∧ ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := by
  first | exact @GlobalTheory.BSP.norm_hf_g_X_and_φ_le | exact GlobalTheory.BSP.norm_hf_g_X_and_φ_le | (intros; apply GlobalTheory.BSP.norm_hf_g_X_and_φ_le <;> assumption)
end
