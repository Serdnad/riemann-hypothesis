module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle443
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSiegelParabolicInvariance
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle444
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle445
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

section Sel

variable {K : Type} [Field K]

def selE (K : Type) [Field K] (r n : ℕ) : Matrix (Fin r) (Fin n) K :=
  fun i j => if (j : ℕ) = i then 1 else 0

theorem selE_mul_transpose {r n : ℕ} (hr : r ≤ n) :
    selE K r n * (selE K r n)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · by_cases hik : i = k
    · subst hik; simp
    · have hne : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
      simp [hik, hne]
  · intro j _ hj
    have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem transpose_selE_mul {r n : ℕ} (hr : r ≤ n) :
    (selE K r n)ᵀ * selE K r n = eId K n r := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selE, eId, Matrix.diagonal_apply]
  by_cases hj : (j : ℕ) < r
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases hjk : j = k
      · subst hjk; simp [hj]
      · have hne : (k : ℕ) ≠ j := fun h => hjk (Fin.ext h.symm)
        simp [hjk, hne]
    · intro i _ hi
      have hne : (j : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i _
      have hne : (j : ℕ) ≠ i := fun h => hj (h ▸ i.2)
      simp [hne]

theorem cT_selE (σ : K →+* K) {r n : ℕ} : cT σ (selE K r n) = (selE K r n)ᵀ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, selE]
  split_ifs <;> simp

theorem extB_eq_selE {r n : ℕ} (hr : r ≤ n) (b : Matrix (Fin r) (Fin r) K) :
    extB (n := n) b = (selE K r n)ᵀ * b * selE K r n := by
  ext i j
  simp only [extB, Matrix.mul_apply, Matrix.transpose_apply, selE]
  by_cases hi : (i : ℕ) < r
  · by_cases hj : (j : ℕ) < r
    · rw [dite_eq_left ⟨hi, hj⟩]
      have e1 : ∀ l : Fin r, (∑ k : Fin r, (if (i : ℕ) = k then (1 : K) else 0) * b k l) = b ⟨i, hi⟩ l := by
        intro l
        rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro k _ hk
          have hne : (i : ℕ) ≠ k := fun h => hk (Fin.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [e1]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro l _ hl
        have hne : (j : ℕ) ≠ l := fun h => hl (Fin.ext h.symm)
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dite_eq_right (fun h => hj h.2)]
      symm
      apply Finset.sum_eq_zero
      intro l _
      have hne : (j : ℕ) ≠ l := fun h => hj (h ▸ l.2)
      simp [hne]
  · rw [dite_eq_right (fun h => hi h.1)]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [Finset.sum_eq_zero, zero_mul]
    intro k _
    have hne : (i : ℕ) ≠ k := fun h => hi (h ▸ k.2)
    simp [hne]

theorem selE_mul_of_isCompl {r n : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) : selE K r n * a = c := by
  ext i j
  simp only [Matrix.mul_apply, selE]
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hr⟩]
  · have key := congrFun (h.2 ⟨i, lt_of_lt_of_le i.2 hr⟩ i.2) j
    simpa using key
  · intro k _ hk
    have hne : (k : ℕ) ≠ i := fun h' => hk (Fin.ext h')
    simp [hne]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end Sel

theorem exists_hermitian_lowerLeft :
    ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n →
      ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K)
        (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K),
        IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C →
        ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧
          C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  intro K _ σ hσ n r hr c a C D T L hc hC hLT hH
  have hca : c = selE K r n * a := (selE_mul_of_isCompl hr hc).symm
  have ha : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hc.1
  have hcTc : cT σ c = cT σ a * (selE K r n)ᵀ := by rw [hca, cT_mul, cT_selE]
  have hcTT : cT σ T * cT σ L = 1 := by rw [← cT_mul, hLT, cT_one]
  have h1 : T * c * cT σ D = D * cT σ a * (selE K r n)ᵀ * cT σ T := by
    rw [← hC, hH, hC, cT_mul, hcTc]
    simp only [Matrix.mul_assoc]
  have hM : D * cT σ a * (selE K r n)ᵀ = T * (c * cT σ D * cT σ L) := by
    calc D * cT σ a * (selE K r n)ᵀ = D * cT σ a * (selE K r n)ᵀ * (cT σ T * cT σ L) := by
          rw [hcTT, Matrix.mul_one]
      _ = T * c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, ← h1]
      _ = T * (c * cT σ D * cT σ L) := by simp only [Matrix.mul_assoc]
  refine ⟨c * cT σ D * cT σ L, ?_, ?_⟩
  · rw [cT_mul, cT_mul, cT_cT σ hσ, cT_cT σ hσ, hcTc]
    calc L * (D * (cT σ a * (selE K r n)ᵀ)) = L * (T * (c * cT σ D * cT σ L)) := by
          rw [← hM]; simp only [Matrix.mul_assoc]
      _ = c * cT σ D * cT σ L := by rw [← Matrix.mul_assoc, hLT, Matrix.one_mul]
  · have hSP : selE K r n * eId K n r = selE K r n := by
      rw [← transpose_selE_mul hr, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hSB : selE K r n * extB (n := n) (c * cT σ D * cT σ L) = (c * cT σ D * cT σ L) * selE K r n := by
      rw [extB_eq_selE hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, selE_mul_transpose hr, Matrix.one_mul]
    have hCa : C * a⁻¹ = T * selE K r n := by
      rw [hC, hca, Matrix.mul_assoc T, Matrix.mul_assoc, ha, Matrix.mul_one]
    rw [hCa, Matrix.mul_assoc T (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_sub (selE K r n), Matrix.mul_one, hSP, hSB,
      sub_self, zero_sub, Matrix.mul_neg, ← transpose_selE_mul hr, ← Matrix.mul_assoc (D * cT σ a), hM]
    simp only [Matrix.mul_assoc, neg_add_cancel]

end GlobalTheory.CompanionTheory.BruhatCell
end

section

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

theorem _root_.GlobalTheory.T.span_range_complement_transform : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det → Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.span_range_lowerLeft <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eisenstein_siegel_parabolic_invariance : PositivityTheory.GramSchwartzFunctions.EC.PInv := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsPInv.pInv | exact GlobalTheory.CompanionTheory.EisCellsPInv.pInv | (intros; apply GlobalTheory.CompanionTheory.EisCellsPInv.pInv <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsAsm

section Compl

variable {K : Type} [Field K]

theorem exists_isCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (hc : LinearIndependent K c) :
    ∃ a : Matrix (Fin n) (Fin n) K, IsCompl c a := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hrW : Module.finrank K W = r := by
    rw [hW, finrank_span_eq_card hc, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hWW'
  rw [hrW, Module.finrank_fin_fun] at hsum
  set m := Module.finrank K W' with hm
  have hn : n = r + m := hsum.symm
  let bW : Module.Basis (Fin m) K W' := Module.finBasisOfFinrankEq K W' hm.symm
  let d : Fin m → (Fin n → K) := fun j => (bW j : Fin n → K)
  have hd : LinearIndependent K d :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span K (Set.range c)) (Submodule.span K (Set.range d)) := by
    refine hWW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hv : LinearIndependent K (Sum.elim c d) := hc.sum_type hd hdisj
  let e : Fin n ≃ Fin r ⊕ Fin m := (finCongr hn).trans finSumFinEquiv.symm
  refine ⟨fun i => Sum.elim c d (e i), ?_, ?_⟩
  · have hli : LinearIndependent K (fun i => Sum.elim c d (e i)) := hv.comp e e.injective
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · intro i hi
    have he : e i = Sum.inl ⟨i, hi⟩ := by
      have : finCongr hn i = Fin.castAdd m ⟨i, hi⟩ := Fin.ext rfl
      simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]
    change Sum.elim c d (e i) = c ⟨i, hi⟩
    rw [he]
    rfl

end Compl

variable {D : D7} {n : ℕ}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sg_sg (D : D7) (x : D.host.E) : sg D (sg D x) = x := by
  show star (star x) = x
  exact star_star x

theorem mat_mul' (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_inv_of (x : G D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (hg : IsUnit g.det)
    (h : mat x = g.map (incA D)) : mat x⁻¹ = g⁻¹.map (incA D) := by
  have h1 : mat x⁻¹ = (mat x)⁻¹ := by
    simp only [mat, map_inv, Matrix.coe_units_inv]
  rw [h1, h]
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul g hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mk_eq_iff_siegel (hR : RatPts) (x y : GF D n) {gx gy : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (hx : IsUnit gx.det) (mx : mat x.1 = gx.map (incA D)) (my : mat y.1 = gy.map (incA D)) :
    mk ((P D n).subgroupOf (GF D n)) x = mk ((P D n).subgroupOf (GF D n)) y ↔ IsSiegelP (gy * gx⁻¹) := by
  have hmem : y.1 * x.1⁻¹ ∈ GF D n := mul_mem y.2 (inv_mem x.2)
  have hmat : mat (y.1 * x.1⁻¹) = (gy * gx⁻¹).map (incA D) := by
    rw [mat_mul', mat_inv_of x.1 hx mx, my, Matrix.map_mul]
  rw [← (hR D n).2.2 _ hmem _ hmat]
  show Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSiegelParabolic_one (K : Type) [Field K] (n : ℕ) : IsSiegelP (1 : Matrix (Fin (n + n)) (Fin (n + n)) K) := by
  unfold IsSiegelP
  intro i j
  exact Matrix.one_apply_ne (finSumFinEquiv.injective.ne Sum.inr_ne_inl)

theorem eisCells_of : Bruhat → RatPts → PInv → Term2 → EisCells := by
  intro hBr hRat hPInv hT2 D n V ψ χ θ μ ω hS Φ hconv μr hμr c hc
  classical
  have ha : ∀ U : Submodule D.host.E (Fin n → D.host.E), ∃ a, IsCompl (c U) a :=
    fun U => exists_isCompl (c U) (hc U).1
  choose a haU using ha
  obtain ⟨hU, huniq⟩ := hBr D.host.E (sg D) (sg_sg D) two_ne_zero n c hc a haU
  have hq : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      ∃ γ ∈ GF D n, mat γ = (repMat (sg D) q.2.1 (a q.1)).map (incA D) :=
    fun q => (hRat D n).2.1 _ (hU q.1 q.2.1 q.2.2).1 (hU q.1 q.2.1 q.2.2).2
  choose γ hγGF hγmat using hq
  have hdet : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      IsUnit (repMat (sg D) q.2.1 (a q.1)).det := fun q => (hU q.1 q.2.1 q.2.2).1
  let f : ((U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U)) →
      GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun q => mk ((P D n).subgroupOf (GF D n)) ⟨γ q, hγGF q⟩
  have hinj : Function.Injective f := by
    intro q q' hqq
    have h1 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q.2.1 (a q.1))⁻¹) :=
      (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ ⟨γ q', hγGF q'⟩ (hdet q) (hγmat q) (hγmat q')).mp hqq
    have h2 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q'.2.1 (a q'.1))⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (hdet q')]
      exact isSiegelParabolic_one _ n
    exact (huniq _ (hdet q') (hU q'.1 q'.2.1 q'.2.2).2).unique h1 h2
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨g, hg, hgu, hgm⟩ := (hRat D n).1 _ (Quotient.out z).2
    obtain ⟨q, hqs, -⟩ := huniq g hg hgu
    refine ⟨q, ?_⟩
    rw [← Quotient.out_eq z]
    exact (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ (Quotient.out z) (hdet q) (hγmat q) hgm).mpr hqs
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hrle : ∀ U : Submodule D.host.E (Fin n → D.host.E), Module.finrank D.host.E U ≤ n := fun U =>
    (Submodule.finrank_le U).trans_eq (Module.finrank_fin_fun _)
  have hsum : Summable (GlobalTheory.Eis.term (P D n) (GF D n) (fun γ => ((ω γ) Φ).1 0) 1) := Summable.of_norm hconv
  have h3 := (e.hasSum_iff).mpr hsum.hasSum
  unfold GlobalTheory.Eis.cosetSum
  convert h3 using 1
  funext q
  have hrel : (⟨γ q, hγGF q⟩ : GF D n) * (Quotient.out (e q))⁻¹ ∈ (P D n).subgroupOf (GF D n) := by
    have h0 : Quotient.mk _ (Quotient.out (e q)) = Quotient.mk _ (⟨γ q, hγGF q⟩ : GF D n) :=
      Quotient.out_eq (f q)
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have hp : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ ∈ (P D n ⊓ GF D n : Subgroup (G D n)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, (GF D n).mul_mem (Quotient.out (e q)).2 ((GF D n).inv_mem (hγGF q))⟩
    have h2 : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ =
        (γ q * ((Quotient.out (e q) : GF D n) : G D n)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [h2]
    exact (P D n).inv_mem hrel
  have hw' := hPInv D n V ψ χ θ μ ω hS Φ _ hp (γ q)
  simp only [inv_mul_cancel_right] at hw'
  simp only [Function.comp_apply, GlobalTheory.Eis.term, mul_one]
  rw [hw']
  exact (hT2 D n V ψ χ θ μ ω hS Φ _ (hrle q.1) (μr _) (hμr _) (c q.1) (a q.1) (haU q.1) q.2
    (γ q) (hγGF q) (hγmat q)).symm

end GlobalTheory.CompanionTheory.EisCellsAsm

end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCells

theorem term_of_covariance : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero →
    PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  intro hHeis hCovar hZero hUnf hTheta D n V ψ χ θ μ ω hS Φ r hr μr hμr c a hc b γ hγ hmat
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hcov⟩, -⟩ := id hS
  have hinv : mat γ * mat γ⁻¹ = 1 := by
    simp only [mat]
    rw [map_inv]
    simp
  rw [hZero D ψ hψ θ hθ V n μ 𝓕 hcov (ω γ Φ).1 (ω γ Φ).2,
    ← hUnf D ψ hψ θ hθ V n r hr μ 𝓕 hcov μr hμr c a hc b Φ.1 Φ.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [← hmat]
  have hΨ := hHeis D ψ hψ θ hθ V n (HMul.hMul (zy y) (mat γ)) Φ.1 Φ.2
  have h1 := hCovar D n V ψ χ θ μ ω hS γ hγ (HMul.hMul (zy y) (mat γ)) Φ
    ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ rfl
  have h2 := hTheta D n V ψ χ θ μ ω hS ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ γ hγ
  have hv : HMul.hMul (HMul.hMul (zy y) (mat γ)) (mat γ⁻¹) = zy y := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hv] at h1
  rw [h1] at h2
  exact h2

end GlobalTheory.CompanionTheory.EisCells
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.sobolev_space_complete : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], SobG →
    ∀ a : ℕ → Mat n → V, (∀ k, Sob μ (a k)) → (∀ w, CauchySeq fun k => cls μ (Rw w (a k))) →
    ∃ b : Mat n → V, Sob μ b ∧ (∀ w, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 (cls μ (Rw w b)))) ∧
      ∀ g ∈ GLs n, Tendsto (fun k => a k g) atTop (𝓝 (b g)) := by
  first | exact @GlobalTheory.CompanionTheory.SobComplete.sob_complete | exact GlobalTheory.CompanionTheory.SobComplete.sob_complete | (intros; apply GlobalTheory.CompanionTheory.SobComplete.sob_complete <;> assumption)
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def m0Z (lam : Fin n → ℤ) : Fin n → ℤ := fun a => 2 * lam a + ((n : ℤ) - 1) - 2 * ((a : ℕ) : ℤ)

def wtR (μ : Fin n → ℤ) : Fin n → ℝ := fun a => (μ a : ℝ)

def DomLE (ν m : Fin n → ℝ) : Prop :=
  (∀ k : ℕ, ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), ν a ≤ ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), m a) ∧
    ∑ a, ν a = ∑ a, m a

def wtDual (E : KMod n) (μ : Fin n → ℤ) : Submodule ℂ (E.V →L[ℂ] ℂ) where
  carrier := {ξ | ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z →
    ξ ∘L E.ρ k⁻¹ = (∏ a, z a ^ μ a) • ξ}
  add_mem' {x y} hx hy k z hk := by
    rw [ContinuousLinearMap.add_comp, hx k z hk, hy k z hk, smul_add]
  zero_mem' k z _ := by simp
  smul_mem' c x hx k z hk := by
    rw [ContinuousLinearMap.smul_comp, hx k z hk, smul_comm]

def IsCliff {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ a b d e, c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : Matrix ι ι ℂ) else 0) ∧
    ∀ a b, (c a b)ᴴ = c b a

def spinM {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b - if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0

def yF {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    Module.End ℂ (ι → V) where
  toFun x := fun i => Kf a b (x i) + ∑ j, spinM c a b i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
    abel
  map_smul' s x := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.CompanionTheory.RealCount
end
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.dominant_hecke_operators_commute : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), (∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t t' : D.T, D.IsDom t → D.IsDom t' → ∀ U U' : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → PositivityTheory.Lbc.IsHeckeOpG π D.J (t' : G) U' → U * U' = U' * U := by
  first | exact @GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | exact GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute | (intros; apply GlobalTheory.CompanionTheory.CassHecke.heckeOp_commute <;> assumption)
end

section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.jacquet_projection_surjective_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J), PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ w ∈ fixed (D.piN π) D.JT, ∃ v : fixed π D.J, D.proj π (v : V) = w := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_surjective <;> assumption)
end
