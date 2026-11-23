module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.TwistFlat.triv_twist_iff | exact GlobalTheory.TwistFlat.triv_twist_iff | (intros; apply GlobalTheory.TwistFlat.triv_twist_iff <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

def lineSubst {K : Type} [Field K] {N : ℕ} (a b : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K →ₐ[K] Polynomial K :=
  aeval fun p : Fin 1 × Fin N => Polynomial.C (a p.2) + Polynomial.C (b p.2) * Polynomial.X

theorem line_eq_lineSubst {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (a b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    line s a b f = lineSubst a b (spec s f) := by
  simp only [line, spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, lineSubst]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K),
      IsScalarTower.algebraMap_apply F K (Polynomial K), AlgHom.commutes]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join, lineSubst]

theorem eval_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) = aeval (join s b) f := by
  simp only [spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K)]
    simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join]

theorem lineSubst_lin {K : Type} [Field K] {N : ℕ} (a b y : Fin N → K) :
    lineSubst a b (lin y) = Polynomial.C (∑ j, a j * y j) + Polynomial.C (∑ j, b j * y j) * Polynomial.X := by

  simp only [lin, lineSubst, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq, add_mul,
  Finset.sum_add_distrib, Polynomial.C_mul, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_lin {K : Type} [Field K] {N : ℕ} (b y : Fin N → K) :
    eval (fun p : Fin 1 × Fin N => b p.2) (lin y) = ∑ j, b j * y j := by
  simp [lin]

theorem coeff_ne_zero_of_resultant_ne_zero {K : Type} [Field K] {δ : ℕ} (hδ : 1 ≤ δ) (P : Polynomial K)
    (hP : P.natDegree ≤ δ) (h : Polynomial.resultant P (Polynomial.derivative P) δ (δ - 1) ≠ 0) : P.coeff δ ≠ 0 := by
  by_contra hc
  apply h
  have hlt : P.natDegree < δ := by
    rcases hP.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at h1
      omega
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h1]; exact hc))
  rcases Nat.lt_or_ge δ 2 with h2 | h2
  · obtain rfl : δ = 1 := by omega
    have hd : Polynomial.derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0), Polynomial.derivative_C]
    simp [hd]
  · apply Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
    calc (Polynomial.derivative P).natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
      _ < δ - 1 := by omega

theorem noSquare_spec_of_disc_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  intro F K _ _ _ D N δ f s a b hδ hdeg hcoeff hdisc
  have hres : (line s a b f).resultant (Polynomial.derivative (line s a b f)) δ (δ - 1) ≠ 0 := hdisc
  have hc : (line s a b f).coeff δ ≠ 0 := coeff_ne_zero_of_resultant_ne_zero hδ _ hdeg hres
  have hspec0 : eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) ≠ 0 := by
    rw [eval_spec, ← hcoeff]
    exact hc
  refine ⟨fun h0 => hspec0 (by rw [h0, map_zero]), fun y _ hdvd => ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  by_cases hβ : ∑ j, b j * y j = 0
  · apply hspec0
    rw [hq, map_mul, map_pow, eval_lin, hβ]
    simp
  · have hnat : (line s a b f).natDegree = δ :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc
    have hP0 : line s a b f ≠ 0 := fun h0 => hc (by rw [h0, Polynomial.coeff_zero])
    have hcop : IsCoprime (line s a b f) (Polynomial.derivative (line s a b f)) := by
      by_contra hnc
      apply hres
      have hd' : (Polynomial.derivative (line s a b f)).natDegree ≤ δ - 1 := by
        rw [← hnat]
        exact Polynomial.natDegree_derivative_le _
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd'
      rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hnat,
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hnc⟩, mul_zero]
    have hQ : line s a b f = lineSubst a b (lin y) * lineSubst a b (lin y) * lineSubst a b q := by
      rw [line_eq_lineSubst, hq, map_mul, map_pow, sq]
    have h1 : lineSubst a b (lin y) ∣ line s a b f :=
      ⟨lineSubst a b (lin y) * lineSubst a b q, by rw [hQ]; ring⟩
    have h2 : lineSubst a b (lin y) ∣ Polynomial.derivative (line s a b f) := by
      refine ⟨Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        lineSubst a b (lin y) * Polynomial.derivative (lineSubst a b q), ?_⟩
      rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_mul]
      ring
    have hu := hcop.isUnit_of_dvd' h1 h2
    rw [lineSubst_lin] at hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [add_comm, Polynomial.natDegree_linear hβ] at hdeg0
    exact one_ne_zero hdeg0

end GlobalTheory.PencilDisc
end
end

section

set_option autoImplicit false

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

theorem prod_pow_natDegree_le_and_coeff {R ι : Type} [CommRing R] (s : Finset ι) (v : ι → Polynomial R) (w m : ι → ℕ)
    (h : ∀ p, (v p).natDegree ≤ w p) :
    (∏ p ∈ s, v p ^ m p).natDegree ≤ ∑ p ∈ s, m p * w p ∧
      (∏ p ∈ s, v p ^ m p).coeff (∑ p ∈ s, m p * w p) = ∏ p ∈ s, (v p).coeff (w p) ^ m p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have h1 : (v p ^ m p).natDegree ≤ m p * w p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2,
      Polynomial.coeff_pow_of_natDegree_le (h p)]

theorem line_natDegree_le_and_coeff (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (u : Fin D → Fin N → R) (a b : Fin N → R) :
    (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧
      (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  classical
  set v : Fin (D + 1) × Fin N → Polynomial R :=
    join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv
  let w : Fin (D + 1) × Fin N → ℕ := fun p => if p.1 = Fin.last D then 1 else 0
  have hdeg : ∀ p, (v p).natDegree ≤ w p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hv, w, join, if_true, Fin.lastCases_last]
      rw [add_comm]
      exact Polynomial.natDegree_linear_le
    · simp [hv, w, join]
  have hco : ∀ p, (v p).coeff (w p) = join u b p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [hv, w, join]
    · simp [hv, w, join]
  have hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ := by
    intro m hm
    have := hf m (by simpa using hm) (Fin.last D)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa [w] using this
    · intro i _ hi
      simp [w, hi]
    · simp
  have hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧
      (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p := by
    intro m hm
    have := prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg
    rw [hsum m hm] at this
    simpa only [hco] using this
  have hline : line u a b f =
      ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p := by
    rw [line, ← hv, aeval_def, eval₂_eq']
    rfl
  rw [hline, aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.coeff_C_mul, (hkey m hm).2]

end GlobalTheory.PencilDisc
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt

namespace GlobalTheory.CMVal.LatEnt

theorem relIndex_congr_radN_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N →
    (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  intro E _ _ N hN
  have := PicFin.finite_quot (E := E) hN.ne'
  let U : Subgroup (Af E)ˣ := congr (fun _ => 1)
  let r : U →* PicFin.intR E ⧸ Ideal.span {(N : PicFin.intR E)} :=
    { toFun := fun u => Ideal.Quotient.mk _ ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩
      map_one' := map_one (Ideal.Quotient.mk _)
      map_mul' := fun a b => by rw [← map_mul]; rfl }
  have h1 : r.toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : ((congr (radN E N)).subgroupOf U).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := r.toHomUnits.ker) fun u hu w => ⟨(u.2 w).1, ?_⟩
    have h2 : Ideal.Quotient.mk (Ideal.span {(N : PicFin.intR E)}) ⟨(u.1 : Af E), fun v =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (u.2 v).1.le⟩ =
        Ideal.Quotient.mk _ 1 := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h2
    obtain ⟨β, hβ⟩ := h2
    have h3 : ((u.1 : (Af E)ˣ) : Af E) - 1 = (N : Af E) * β.1 := congrArg Subtype.val hβ
    rw [← map_natCast (algebraMap E (Af E))] at h3
    have h4 : ((u.1 : (Af E)ˣ) : Af E) w - 1 = algebraMap E (w.adicCompletion E) (N : E) * β.1 w :=
      congrArg (fun z : Af E => z w) h3
    show Valued.v (((u.1 : (Af E)ˣ) : Af E) w - 1) ≤ Valued.v (N : w.adicCompletion E)
    rw [h4, map_mul, map_natCast]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (β.2 w))
  exact h2.1

end GlobalTheory.CMVal.LatEnt
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem gm_of_isPullGen {X Y Z : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) (ψ : Z ⟶ X) (z : Z) (k l : M.ι) (hk : p (ψ z) ∈ M.U k) (hl : p (ψ z) ∈ M.U l) :
    gm ψ z (p ⁻¹ᵁ M.U k) (e k) = gm (ψ ≫ p) z (M.U k ⊓ M.U l) (M.g k l) * gm ψ z (p ⁻¹ᵁ M.U l) (e l) := by
  have hm : ψ z ∈ p ⁻¹ᵁ (M.U k ⊓ M.U l) := ⟨hk, hl⟩
  have h := congrArg (gm ψ z (p ⁻¹ᵁ (M.U k ⊓ M.U l)))
    (he k l (p ⁻¹ᵁ (M.U k ⊓ M.U l)) (fun _ hy => hy.1) (fun _ hy => hy.2) le_rfl)
  exact (gm_res _ _ _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_res _ _ _ hm _).trans (gm_pull ψ p z _ hm _)) (gm_res _ _ _ hm _))))

theorem gm_pull_of_isPullGen {X Y X₂ Y₂ : Scheme.{0}} {p : X ⟶ Y} {M : LB Y} {e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ}
    (he : IsPullGen p M e) {P : X₂ ⟶ Y₂} {φ : Y₂ ⟶ Y} {ψ : X₂ ⟶ X} (h : P ≫ φ = ψ ≫ p) (x : X₂)
    (J J' : PUnit → M.ι) (hJ : P x ∈ (M.pull φ).U J) (hJ' : P x ∈ (M.pull φ).U J') :
    gm ψ x (p ⁻¹ᵁ M.U (J PUnit.unit)) (e (J PUnit.unit)) =
      gm P x ((M.pull φ).U J ⊓ (M.pull φ).U J') ((M.pull φ).g J J') *
        gm ψ x (p ⁻¹ᵁ M.U (J' PUnit.unit)) (e (J' PUnit.unit)) := by
  rw [gm_pull_g M φ P x J J' hJ hJ', h]
  exact gm_of_isPullGen he ψ x _ _ (preimage_le_of_comp h _ (mem_pull.1 hJ)) (preimage_le_of_comp h _ (mem_pull.1 hJ'))

theorem gm_res_pullU {X Z : Scheme.{0}} (ψ : Z ⟶ X) (z : Z) (U : X.Opens) {V : Z.Opens} (hle : V ≤ ψ ⁻¹ᵁ U)
    (hz : z ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU ψ U a)) = gm ψ z U a :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) ψ z U (hle hz) a).trans (by rw [Category.id_comp]))

theorem germ_addGen_pullGen {S : Scheme.{0}} {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι)
    (x : (A ⊗ (A ⊗ T)).left) (hx : x ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    gm (𝟙 _) x _ (addGen q M e k) =
      gm (ptFst A T).left x _ (e (k.1.1 PUnit.unit)) * gm (ptSnd A T).left x _ (e (k.1.2 PUnit.unit)) *
        (gm (ptMul A T).left x _ (e (k.2 PUnit.unit)))⁻¹ := by
  rw [addGen, map_mul, map_mul, map_inv, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx, gm_res_pullU _ _ _ _ hx]

theorem isPullGen_addGen : ∀ (S : Scheme.{0}) (A A' T : Over S) [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsPullGen (pmap q T).left M e → IsPullGen (pmap2 q T).left (addBundle M) (addGen q M e) := by
  intro S A A' T _ _ q _ M e he k l W h₁ h₂ h₃
  refine unit_ext fun x hx => ?_
  have hk := h₁ hx
  have hl := h₂ hx
  have e₁ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_fst q T) x k.1.1 l.1.1 hk.1.1 hl.1.1
  have e₂ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_snd q T) x k.1.2 l.1.2 hk.1.2 hl.1.2
  have e₃ := gm_pull_of_isPullGen he (prodMapPairTimesIdentity_mul q T) x k.2 l.2 hk.2 hl.2
  have g := (gm_div _ _ (pmap2 q T).left x k l ⟨hk, hl⟩).trans
    (congrArg (· * _) (gm_tens _ _ (pmap2 q T).left x k.1 l.1 hk.1 hl.1))
  refine ((gm_res (𝟙 _) x h₁ hx _).trans (germ_addGen_pullGen q M e k x hk)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res_pullU _ x _ h₃ hx _).trans g)
    ((gm_res (𝟙 _) x h₂ hx _).trans (germ_addGen_pullGen q M e l x hl)))).trans ?_
  rw [e₁, e₂, e₃, mul_inv]
  have alg : ∀ {G : Type} [CommGroup G] (a b c u v w : G),
      a * b * c⁻¹ * (u * v * w⁻¹) = a * u * (b * v) * (c⁻¹ * w⁻¹) := by
    intro G _ a b c u v w
    ac_rfl
  exact alg _ _ _ _ _ _

end GlobalTheory.CharKer
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer.PmapTwo

variable {S : Scheme.{0}}

theorem isPullback_whiskerLeft_left (W : Over S) {G B : Over S} (p : G ⟶ B) :
    IsPullback (W ◁ p).left (snd W G).left (snd W B).left p.left := by
  have h1 : IsPullback (fst W B).left (snd W B).left W.hom B.hom := IsPullback.of_hasPullback W.hom B.hom
  have h2 : IsPullback (fst W G).left (snd W G).left W.hom G.hom := IsPullback.of_hasPullback W.hom G.hom
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerLeft_fst, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]

theorem isPullback_whiskerRight_left {G B : Over S} (p : G ⟶ B) (W : Over S) :
    IsPullback (p ▷ W).left (fst G W).left (fst B W).left p.left := by
  have h1 : IsPullback (snd B W).left (fst B W).left W.hom B.hom :=
    (IsPullback.of_hasPullback B.hom W.hom).flip
  have h2 : IsPullback (snd G W).left (fst G W).left W.hom G.hom := (IsPullback.of_hasPullback G.hom W.hom).flip
  refine IsPullback.of_right ?_ ?_ h1
  · rw [← Over.comp_left, whiskerRight_snd, Over.w p]; exact h2
  · rw [← Over.comp_left, ← Over.comp_left, whiskerRight_fst]

theorem prodMapPairTimesIdentity_eq_comp_whiskers {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    pmap2 q T = (q ▷ (A ⊗ T)) ≫ (A' ◁ (q ▷ T)) := by
  ext <;> simp [pmap2, pmap]

end GlobalTheory.CharKer.PmapTwo


open GlobalTheory.CharKer.PmapTwo in
theorem GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom :
    ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left →
      Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  intro S A A' T q h1 h2 h3
  have hR := (isPullback_whiskerRight_left q (A ⊗ T)).flip
  have hL := (isPullback_whiskerLeft_left A' (q ▷ T)).flip
  have hR' := (isPullback_whiskerRight_left q T).flip
  have a1 : Flat (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h1
  have a2 : Surjective (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h2
  have a3 : IsAffineHom (q ▷ (A ⊗ T)).left := MorphismProperty.of_isPullback hR h3
  have b1 : Flat (q ▷ T).left := MorphismProperty.of_isPullback hR' h1
  have b2 : Surjective (q ▷ T).left := MorphismProperty.of_isPullback hR' h2
  have b3 : IsAffineHom (q ▷ T).left := MorphismProperty.of_isPullback hR' h3
  have c1 : Flat (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b1
  have c2 : Surjective (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b2
  have c3 : IsAffineHom (A' ◁ (q ▷ T)).left := MorphismProperty.of_isPullback hL b3
  rw [prodMapPairTimesIdentity_eq_comp_whiskers, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end

section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

end GlobalTheory.SphPar
end
