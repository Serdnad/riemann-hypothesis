module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import GroundTheory.Brauer.TensorSimple
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle012
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_family_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) → ∀ g' : ∀ t, F.obj (G.obj t), (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), g' t' = mp F (G.map a) (g' t)) → ∃ g : C0 F, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), g T' = mp F φ (g T)) ∧ ∀ t, g (G.obj t) = g' t := by
  intro R _ C _ C' _ F G hsep hglue g' hg'
  choose g hg using fun T : C ↦ hglue T (fun t _ ↦ g' t) fun t t' _ a ↦ hg' a
  refine ⟨g, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · refine sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)
    rw [map_sub, ← mp_comp, hg, hg, sub_self]
  · have h := hg (G.obj t) t (𝟙 _)
    rwa [mp_id] at h

end GlobalTheory
end

section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory


open Filter Topology in
open Filter Topology TopologicalSpace TensorProduct in
theorem _root_.GlobalTheory.tensor_hol_ext_of_values :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] _root_.GlobalTheory.AnPer.Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  intro E _ _ W D _ _ x y h
  classical
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hzp : ∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D)
      ((Algebra.ofId ℂ D).comp (_root_.GlobalTheory.AnPer.Hol.ev p hp))
      (fun _ _ ↦ Commute.all _ _) z = 0 := fun p hp => by
    rw [hz, map_sub, h p hp, sub_self]
  let b := Module.Free.chooseBasis ℂ D
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := _root_.GlobalTheory.AnPer.Hol W) b
  have hc : ∀ i, e z i = 0 := by
    intro i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    have hzero : (0 : _root_.GlobalTheory.AnPer.Hol W).fn p = 0 := by
      rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_zero]
    have h0 := hzp p hp

    rw [← e.symm_apply_apply z, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum,
    map_sum] at h0
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
      _root_.GlobalTheory.AnPer.Hol.ev_apply, Algebra.ofId_apply] at h0
    have h1 : ∑ j ∈ (e z).support, (e z j).fn p • b j = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    by_cases hi : i ∈ (e z).support
    · rw [linearIndependent_iff'.1 b.linearIndependent (e z).support (fun j => (e z j).fn p) h1 i hi,
        hzero]
    · rw [Finsupp.notMem_support_iff.1 hi]
  exact e.injective (by rw [map_zero]; exact Finsupp.ext hc)

end GlobalTheory
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem charpoly_psi_eq_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C)
    (hdeg : (minpoly G.F γ).natDegree = G.n) :
    (G.psi v γ).charpoly = (minpoly G.F γ).map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) ((minpoly G.F γ).map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : ((minpoly G.F γ).map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : ((minpoly G.F γ).map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem charpoly_psi_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (g : G.C),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).Separable → (G.psi v g).charpoly.Separable := by
  intro p _ G v g hdeg hsep
  rw [charpoly_psi_eq_map_minpoly G v g hdeg]
  exact hsep.map

end GlobalTheory.LKMid
end
end

section

open Matrix GlobalTheory.LKTrip Finset

namespace GlobalTheory.SigDiag

theorem eigenvalues_multiset_eq {n : ℕ} (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian) :
    Multiset.map hA.eigenvalues univ.val = Multiset.map r univ.val := by
  have h3 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at h3
  · have h4 := congrArg (Multiset.map Complex.re) h3
    simp only [Polynomial.roots_X_sub_C, Multiset.map_map] at h4
    simpa [Function.comp_def, Multiset.bind_singleton] using h4.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

theorem card_subtype_eq_of_multiset {n : ℕ} {f g : Fin n → ℝ}
    (h : Multiset.map f univ.val = Multiset.map g univ.val) (P : ℝ → Prop) [DecidablePred P] :
    Fintype.card {i // P (f i)} = Fintype.card {i // P (g i)} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have e : ∀ k : Fin n → ℝ, (univ.filter fun i => P (k i)).card =
      Multiset.countP P (Multiset.map k univ.val) := by
    intro k
    rw [Multiset.countP_map, Finset.card_def, Finset.filter_val]
  rw [e f, e g, h]

end GlobalTheory.SigDiag

namespace GlobalTheory.LKTrip

theorem sigPosH_sigNegH_diagonal : ∀ (n : ℕ) (r : Fin n → ℝ)
    (hA : (Matrix.diagonal (fun i => ((r i : ℝ) : ℂ))).IsHermitian),
    sigPosH hA = Fintype.card {i // 0 < r i} ∧ sigNegH hA = Fintype.card {i // r i < 0} := by
  intro n r hA
  have h := GlobalTheory.SigDiag.eigenvalues_multiset_eq r hA
  exact ⟨GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => 0 < x),
    GlobalTheory.SigDiag.card_subtype_eq_of_multiset h (fun x => x < 0)⟩

end GlobalTheory.LKTrip
end

section

open GlobalTheory.LKTrip NumberField

namespace GlobalTheory.HTGroupOver

theorem exists_gen {F : Type} [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) :
    ∃ y : Kq, ∃ r : ℚ, (y : F) * y = r ∧ IsCMField.complexConj F (y : F) = -(y : F) ∧
      ∀ z : Kq, ∃ a b : ℚ, (z : F) = a + b * y := by
  classical
  let σ : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨x0, hx0K, hx0⟩ := hKq.2 σ
  let x : Kq := ⟨x0, hx0K⟩
  have hσq : ∀ q : ℚ, (σ (q : F)).im = 0 := by intro q; simp [map_ratCast]
  have hdep : ¬ LinearIndependent ℚ ![(1 : Kq), x, x * x] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [hKq.1] at this
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hgF : (g 0 : F) + g 1 * x0 + g 2 * (x0 * x0) = 0 := by
    have := congrArg (fun w : Kq => (w : F)) hg
    simpa [Rat.smul_def, x] using this

  have hnr : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * x0 ≠ 0 := by
    intro a b hb h
    have h2 := congrArg (fun w => (σ w).im) h
    simp only [map_add (f := _), map_mul, map_ratCast, Complex.add_im, Complex.ratCast_im, Complex.mul_im,
      Complex.ratCast_re, zero_mul, add_zero, zero_add, map_zero, Complex.zero_im] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact hb (by exact_mod_cast h3)
    · exact hx0 h3
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2] at hgF
    simp only [Rat.cast_zero, zero_mul, add_zero] at hgF
    by_cases h1 : g 1 = 0
    · rw [h1] at hgF
      simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hgF
      fin_cases i <;> simp_all
    · exact hnr _ _ h1 hgF
  let y0 : F := 2 * g 2 * x0 + g 1
  have hy0K : y0 ∈ Kq := by
    refine add_mem (mul_mem (mul_mem (ofNat_mem Kq 2) (SubfieldClass.ratCast_mem Kq _)) hx0K)
      (SubfieldClass.ratCast_mem Kq _)
  have hy0sq : y0 * y0 = ((g 1 ^ 2 - 4 * g 0 * g 2 : ℚ) : F) := by
    push_cast
    linear_combination (4 * (g 2 : F)) * hgF
  have hy0ne : ∀ a b : ℚ, b ≠ 0 → (a : F) + b * y0 ≠ 0 := by
    intro a b hb h
    apply hnr (a + b * g 1) (2 * b * g 2) (by simp [hb, hg2])
    push_cast
    linear_combination h

  let y : Kq := ⟨y0, hy0K⟩
  refine ⟨y, g 1 ^ 2 - 4 * g 0 * g 2, hy0sq, ?_, ?_⟩
  · have hc : (IsCMField.complexConj F y0 - y0) * (IsCMField.complexConj F y0 + y0) = 0 := by
      have h1 : IsCMField.complexConj F y0 * IsCMField.complexConj F y0 = y0 * y0 := by
        rw [← map_mul, hy0sq, map_ratCast]
      linear_combination h1
    rcases mul_eq_zero.1 hc with h | h
    · exfalso
      have h1 : IsCMField.complexConj F y0 = y0 := sub_eq_zero.1 h
      have h2 := IsCMField.complexEmbedding_complexConj F σ y0
      rw [h1] at h2
      have h3 := congrArg Complex.im h2
      simp only [Complex.conj_im] at h3
      have h4 : (σ y0).im = 0 := by linarith
      have h5 : (σ y0).im = 2 * g 2 * (σ x0).im := by
        have e : σ y0 = ((2 * g 2 : ℚ) : ℂ) * σ x0 + ((g 1 : ℚ) : ℂ) := by
          simp only [y0, map_add (f := _), map_mul, map_ratCast, map_ofNat]; push_cast; ring
        rw [e, Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.ratCast_im]
        push_cast; ring
      rw [h5] at h4
      rcases mul_eq_zero.1 h4 with h6 | h6
      · rcases mul_eq_zero.1 h6 with h7 | h7
        · norm_num at h7
        · exact hg2 (by exact_mod_cast h7)
      · exact hx0 h6
    · exact eq_neg_of_add_eq_zero_left h
  · have hli : LinearIndependent ℚ ![(1 : Kq), y] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      have ha' := congrArg (fun w : Kq => (w : F)) ha
      simp only [Rat.smul_def, mul_one] at ha'
      apply hy0ne (-a) 1 one_ne_zero
      push_cast at ha' ⊢
      simp only [y] at ha'
      rw [← ha']
      ring
    have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hKq.1])
    intro z
    have hz : z ∈ Submodule.span ℚ (Set.range ![(1 : Kq), y]) := by rw [hsp]; trivial
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp [Rat.smul_def, y]

theorem liesOver_or_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p),
    LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  intro p _ G τ
  obtain ⟨y, r, hyr, hcy, hspan⟩ := exists_gen G.Kq G.hKq
  have hyK : y * y = (r : G.Kq) := Subtype.ext (by push_cast; exact hyr)
  have hsq : τ (y : G.F) * τ (y : G.F) =
      algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) * algebraMap ℚ_[p] (PadicAlgCl p) (G.u y) := by
    rw [← map_mul, ← map_mul, ← map_mul, hyK, hyr, map_ratCast, map_ratCast, map_ratCast]
  have hz : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * y := by
    intro z
    obtain ⟨a, b, h⟩ := hspan z
    exact ⟨a, b, Subtype.ext (by push_cast; exact h)⟩
  rcases mul_self_eq_mul_self_iff.1 hsq with h | h
  · left
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add (f := _), map_mul, map_ratCast, h]
  · right
    intro z
    obtain ⟨a, b, rfl⟩ := hz z
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, conjQ_apply,
      Subfield.coe_add, Subfield.coe_mul, SubfieldClass.coe_ratCast, map_add, map_mul, map_ratCast, hcy, map_neg, h]
    ring

end GlobalTheory.HTGroupOver
end

section

noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

abbrev Qv (v : AwayP p) : Type := v.1.adicCompletion ℚ

abbrev Gv (G : HTGroup p) (v : AwayP p) : Type := UPts G.star (Qv v)

def piV (G : HTGroup p) (v : AwayP p) : G.GAf →* Gv G v := ubcMap (AfP.eval v)

def basV (G : HTGroup p) (v : AwayP p) : Module.Basis (Fin (Module.finrank ℚ G.C)) (Qv v) (Qv v ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (Qv v) (Module.finBasis ℚ G.C)

def IsIntV (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) : Prop :=
  ∀ i, (basV G v).repr y i ∈ v.1.adicCompletionIntegers ℚ

def IntV (G : HTGroup p) (v : AwayP p) : Set (Gv G v) :=
  {g | IsIntV G v (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    IsIntV G v ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ) ∧
    (((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ)}

theorem inv_mem_IntV (G : HTGroup p) (v : AwayP p) {g : Gv G v} (h : g ∈ IntV G v) : g⁻¹ ∈ IntV G v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h2
  · simpa using h1
  · exact h4
  · simpa using h3

end GlobalTheory.OrbFinAf
end
end

section

noncomputable section

open GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.TorCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.TorCls
end
end

section

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma Matrix

def stdH (K : UQ) (n : ℕ) (y z : Fin n → K.E) : K.E := ∑ k, y k * K.c (z k)

def IsModel {K : UQ} (B : InvAlg K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) : Prop :=
  B.σ (x : B.A) = x ∧ (∀ y, ψ (B.g * y) = γ *ᵥ ψ y) ∧ ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z

end GlobalTheory.InertUnitOrb
end
end

section

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.flat_B : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  intro R _ _ i
  haveI : Module.Flat i.A i.B := IsLocalization.flat i.B i.q.primeCompl
  exact Module.Flat.trans R i.A i.B

end GlobalTheory.Henselisation
end
