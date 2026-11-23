module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.charPolyRat : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f.asHom]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (AddMonoidAlgebra.coeff F d * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [ite_eq_right]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← zsmul_one (R := End A) n, End.sub_asHom, End.smul_asHom, End.one_asHom, sub_eq_add_neg]
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_monic_rat_charPoly_abelianVariety : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f.asHom]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (AddMonoidAlgebra.coeff F d * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [ite_eq_right]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = AddMonoidAlgebra.coeff F (Finsupp.single 0 N) := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, one_smul]
    rw [← zsmul_one (R := End A) n, End.sub_asHom, End.smul_asHom, End.one_asHom, sub_eq_add_neg]
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def LocCond (w : Pl D.host.E) (inPg inQ : Prop) (r t : ℕ) {m : ℕ} (g : GL (Fin m) (Kw w)) : Prop :=
  g ∈ KO (Kw w) (Fin m) ∧
    (inPg → (∀ a b : Fin m, Formalism.L2.DIV.blkOf r t b < Formalism.L2.DIV.blkOf r t a → valuation (Kw w) (g.1 a b) < 1) ∧
      ∀ a b : Fin m, a.val < r → b.val < r → valuation (Kw w) ((g.1 - 1) a b) < 1) ∧
    (inQ → ∀ a b : Fin m, Formalism.L2.DIV.blk2 r b < Formalism.L2.DIV.blk2 r a → valuation (Kw w) (g.1 a b) < 1)

theorem inBasis_mem_iff {n m : ℕ} (hm : m = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin m) (Kw w))) (p q : Prop) (r t : ℕ) (hK : ∀ g, g ∈ K ↔ LocCond w p q r t g) :
    inBasis hm β w x ∈ K ↔ LocCond w p q r t (inBasis rfl β w x) := by
  subst hm; exact hK _

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ)
    (hg : g ∈ blockTri (blk2 r)) :
    upperLeftBlock hr g = 1 ↔ ∀ a b : Fin n, a.val < r → b.val < r →
      (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin n) (Fin n) κ) a b := by
  unfold upperLeftBlock
  rw [extendOne_of_mem _ hg]
  constructor
  · intro h a b ha hb
    have e := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩) h
    have e2 : (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := e
    rw [e2, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h' => hab (Fin.ext (Fin.mk.inj h')))]
  · intro h
    apply Units.ext
    ext i j
    have e := h (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2
    show (g : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr i) (Fin.castLE hr j) = (1 : Matrix (Fin r) (Fin r) κ) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.castLE_injective hr h'))]

theorem levelChainTypePlaces_subset_chosenPlaces {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    L.Pg ⊆ G.pl.W0 := by
  classical
  intro PP hP
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    simpa using hg
  have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hw : G.pl.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ∈ L.Pg := G.pl.w_g _ k hv
  have he : (G.pl.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))).under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := G.pl.under_w hS
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq he with e | e
  · rw [← e]; exact Finset.mem_image_of_mem _ hS
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) ((GlobalTheory.StepLifts.places_apart L hL t).1 PP hP _ (Or.inl hw))

theorem prodLev_inf_UA {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : Lev.IsBaseFrame V β Λ 1) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (Ld : LevDat D.host.E ℂ V.rank) (hH : Ld.P.H = ⊥)
    (hPg : Ld.Pg ⊆ P) (hQ : Ld.Q ⊆ P)
    (hK : ∀ w : P, ∀ g, g ∈ K w ↔ LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t g) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = lev D.sp.cm V.gram β Ld := by
  have hloc : ∀ (w : P) x, inBasis (hn w) β w.1 x ∈ K w ↔
      LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
    fun w x => inBasis_mem_iff (hn w) β x w.1 (K w) _ _ _ _ (hK w)
  have red0 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j = 0 ↔
        valuation (Kw PP) ((inBasis rfl β PP x).1 i j) < 1 := by
    intro x hx PP i j
    have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
    simpa using e
  have red1 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j =
          (1 : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j ↔
        valuation (Kw PP) (((inBasis rfl β PP x).1 - 1) i j) < 1 := by
    intro x hx PP i j
    by_cases hij : i = j
    · subst hij
      have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i i 1
      simpa [Matrix.one_apply] using e
    · have e := GlobalTheory.T.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
      simpa [Matrix.one_apply, hij] using e
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hA : ∀ w : P, LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
      fun w => (hloc w x).1 (Subgroup.mem_iInf.1 h1 w)
    have hSt : x ∈ St β := GlobalTheory.T.mem_latticeStabilizer_of_local_integral_inBasis β x fun w => by
      by_cases hw : ∃ w0 ∈ P, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
      · obtain ⟨w0, hw0, e⟩ := hw
        have hK0 := (hA ⟨w0, hw0⟩).1
        rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
        · exact hK0
        · exact GlobalTheory.T.integralGL_conjPlace_of_selfDual_baseFrame V β Λ hβ x hU w0 hK0
      · push_neg at hw
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw
    have hgP : ∀ PP ∈ Ld.Pg, redFn β PP x ∈ blockTri (blkOf Ld.r Ld.t) := fun PP hP => by
      rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 (((hA ⟨PP, hPg hP⟩).2.1 hP).1 a b hab)
    refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hSt, hgP, fun PP hP => ?_⟩, ?_⟩
    · rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 ((hA ⟨PP, hQ hP⟩).2.2 hP a b hab)
    · rw [hH, Subgroup.mem_bot]
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 x) = 1
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hgP PP.1 PP.2))]
      intro a b ha hb
      exact (red1 x hSt PP.1 a b).2 (((hA ⟨PP.1, hPg PP.2⟩).2.1 PP.2).2 a b ha hb)
  · intro hx
    obtain ⟨hpar, hr⟩ := mem_lev.1 hx
    obtain ⟨hU, hSt, hg, hq⟩ := mem_parLev.1 hpar
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => (hloc w x).2 ⟨inBasis_mem_KO β x hSt w.1, fun hw => ⟨?_, ?_⟩,
      fun hw a b hab => (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hq w.1 hw) a b hab)⟩,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β x hSt w'⟩, hU⟩
    · intro a b hab
      exact (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hg w.1 hw) a b hab)
    · intro a b ha hb
      rw [hH, Subgroup.mem_bot] at hr
      have e : upperLeftBlock Ld.hr (redFn β w.1 x) = 1 := congrFun hr ⟨w.1, hw⟩
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hg w.1 hw))] at e
      exact (red1 x hSt w.1 a b).1 (e a b ha hb)

theorem givenLevel_zero_iff {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (k : ℕ)
    (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) :
    g ∈ givenLevel G t w (0, k) ↔ g ∈ (stepGroup L t w k).map (reGL (ixFin G t w k)).toMonoidHom := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Iff.rfl

theorem levRow_zero_eq_lev : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m),
    HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  intro D T L sc G W U S μ₀ hL t h
  classical
  have hr : D.R.r ≤ (G.V (.grid 0 D.R.m)).rank := by rw [← rank_zero_m G]; exact r_le_X
  have hbase : Lev.IsBaseFrame (G.V (.grid 0 D.R.m)) (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) 1 := by
    obtain ⟨c, hc⟩ := hL.βX
    rw [one_pow] at hc
    have key : ∀ (X Y : LSp D) (a : GL (Fin X.sp.rank) (Lev.EAf D)) (b : GL (Fin Y.sp.rank) (Lev.EAf D)),
        X = Y → HEq a b → Lev.IsBaseFrame Y.sp b Y.lat 1 → Lev.IsBaseFrame X.sp a X.lat 1 := by
      rintro X _ a b rfl hab h'
      rwa [eq_of_heq hab]
    exact key _ ⟨D.sp.X', L.ΛX⟩ _ _ (colY_m L) (colFrame_m L) hc
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hdis := (GlobalTheory.StepLifts.places_apart L hL t).2
  have core := prodLev_inf_UA hbase (locPl G t) (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩)
    (fun w => givenLevel G t w (0, D.R.m))
    (Lev.datY (G.V (.grid 0 D.R.m)).rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B) rfl
    (fun PP hP => Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t hP)) (fun PP hP => Finset.mem_union_right _ hP)
    (fun w g => by
      rw [givenLevel_zero_iff G t w.1 D.R.m hm]
      by_cases hP : w.1 ∈ L.Pg
      · have hnq : w.1 ∉ L.Q t := Finset.disjoint_left.1 hdis hP
        rw [GlobalTheory.T.thetaGridBlockCongruence_typePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun _ => ⟨h2, h3⟩, fun hq => absurd hq hnq⟩
        · rintro ⟨h1, h2, -⟩
          exact ⟨h1, (h2 hP).1, (h2 hP).2⟩
      · rw [GlobalTheory.T.thetaGridBlockCongruence_offTypePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hp => absurd hp hP, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩)
  have e1 : S.levRow t 0 h = prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩) (fun w => givenLevel G t w (0, D.R.m)) := rfl
  rw [e1, core]
  have key2 : ∀ (X : LSp D), X = ⟨D.sp.X', L.ΛX⟩ → ∀ (b : GL (Fin X.sp.rank) (Lev.EAf D)), HEq b L.βX →
      ∀ (hr : D.R.r ≤ X.sp.rank),
      HEq (lev D.sp.cm X.sp.gram b (Lev.datY X.sp.rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B))
        (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
    rintro X rfl b hb hr
    cases eq_of_heq hb
    rfl
  exact key2 (G.node (.grid 0 D.R.m)) (colY_m L) _ (colFrame_m L) hr

end GlobalTheory.FunObj
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem liftsAlong_of_smooth_inj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ g hA hg U M hU hM hI B _ _ t ht hsq
  have : Smooth U.hom := hU.smooth
  have : LocallyOfFiniteType U.hom := inferInstance
  have hF : FieldChart A M := fieldChart_of_inj _ A hA g hg U M hU hM hI
  have hT : TanLift A M := tanLift_of_fieldChart _ A hA U M hM hI hF
  have hS : SmallLift A M := GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting _ A hA U M hM hI hT
  exact GlobalTheory.T.liftsAlong_principal_small_extension R A U M hM hS B t ht hsq

end GlobalTheory.DualOpen
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  first | exact @GlobalTheory.InertBridge.fix_vac | exact GlobalTheory.InertBridge.fix_vac | (intros; apply GlobalTheory.InertBridge.fix_vac <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.uniformisation_goodEmbedding_independent_readings : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ i σ, GoodEmb T.Q.c (res T σ) → (∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b → LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k)) ∧ Submodule.span ℂ (Set.range (jTop T R κ v₀ i σ)) = ⊤ := by
  first | exact @GlobalTheory.UnifGood.unif_good | exact GlobalTheory.UnifGood.unif_good | (intros; apply GlobalTheory.UnifGood.unif_good <;> assumption)
end
