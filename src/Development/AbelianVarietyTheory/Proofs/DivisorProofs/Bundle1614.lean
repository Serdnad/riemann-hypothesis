module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
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
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussAbsMulSupportFinite
import ReciprocityTheory.SemistableReduction.Bundle008
import ReciprocityTheory.SemistableReduction.Bundle013
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFinPart

theorem log_gaussAbs_support_finite {E : Type} [Field E] [NumberField E] {σ : Type}
    (g : MvPolynomial σ E) :
    (Function.support fun v : FinitePlace E => Real.log (gaussAbs v g)).Finite :=
  ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_support_finite g

theorem finPart_props : ∀ (E : Type) [Field E] [NumberField E] (σ τ : Type),
    (∀ g : MvPolynomial σ E, g ≠ 0 → {v : FinitePlace E | gaussAbs v g ≠ 1}.Finite ∧
      ∀ v : FinitePlace E, 0 < gaussAbs v g) ∧
    (∀ (g : MvPolynomial σ E) (g' : MvPolynomial τ E), g ≠ 0 → g' ≠ 0 →
      (∀ v : FinitePlace E, gaussAbs v g' ≤ gaussAbs v g) → finPart g' ≤ finPart g) ∧
    ∀ (g : MvPolynomial σ E) (m : σ →₀ ℕ), g.coeff m ≠ 0 →
      -mean E (fun s => Real.log ‖s (g.coeff m)‖) ≤ finPart g := by
  intro E _ _ σ τ
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  refine ⟨fun g hg => ⟨?_, fun v => gauss_abs_pos_of_ne_zero v g hg⟩, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite g hg
  · intro g g' hg hg' hle
    unfold finPart
    refine div_le_div_of_nonneg_right ?_ hd.le
    exact finsum_le_finsum' (log_gaussAbs_support_finite g') (log_gaussAbs_support_finite g)
      (fun v => Real.log_le_log (gauss_abs_pos_of_ne_zero v g' hg') (hle v))
  · intro g m hm
    have hg : g ≠ 0 := by
      rintro rfl; exact hm (by simp)
    set c := g.coeff m with hc
    have h1 : ∑ᶠ v : FinitePlace E, Real.log (v c) ≤ ∑ᶠ v : FinitePlace E, Real.log (gaussAbs v g) :=
      finsum_le_finsum'
        ((FinitePlace.hasFiniteMulSupport hm).subset (by
          intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one]))
        (log_gaussAbs_support_finite g)
        (fun v => Real.log_le_log (FinitePlace.pos_iff.mpr hm) (coeff_le_gauss_abs v g m))
    rw [ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm c hm] at h1
    unfold mean finPart
    rw [sum_log_norm_embedding_eq c hm, ← neg_div]
    exact div_le_div_of_nonneg_right h1 hd.le

end GlobalTheory.HSFinPart
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.HyperplaneFactor

theorem eval_lin {K : Type} [Field K] {N : ℕ} (x : Fin 1 × Fin N → K) (y : Fin N → K) :
    eval x (lin y) = ∑ j, x (0, j) * y j := by
  simp [lin]

theorem coeff_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) (j : Fin N) :
    AddMonoidAlgebra.coeff (lin y) (Finsupp.single ((0 : Fin 1), j) 1) = y j := by
  classical
  rw [lin, coeff_sum]
  simp only [mul_comm (X _) (C _), coeff_C_mul, coeff_X', Finsupp.single_left_inj (one_ne_zero' ℕ)]
  simp

theorem isHomogeneous_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X K _).mul (isHomogeneous_C _ _)

theorem irreducible_lin {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : Irreducible (lin y) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have h0 : lin y ≠ 0 := fun h => hj (by
    have := coeff_lin y j
    simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact this.symm)
  refine irreducible_of_totalDegree_eq_one ((isHomogeneous_lin y).totalDegree h0) fun x hx => ?_
  have hd := hx (Finsupp.single (0, j) 1)
  rw [coeff_lin] at hd
  exact isUnit_of_dvd_unit hd (IsUnit.mk0 _ hj)

theorem exists_dvd_pow_of_zeros {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {a b : MvPolynomial (Fin 1 × Fin N) K}
    (h : ∀ x, eval x a = 0 → eval x b = 0) : ∃ n : ℕ, a ∣ b ^ n := by
  have hb : b ∈ (Ideal.span {a}).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have h1 := hx a (Ideal.subset_span rfl)
    have e : ∀ p : MvPolynomial (Fin 1 × Fin N) K, aeval x p = eval x p := fun p =>
      DFunLike.congr_fun (coe_aeval_eq_eval x) p
    rw [e] at h1
    change aeval x b = 0
    rw [e]
    exact h x h1
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem eq_C_mul_prod_lin : ∀ (K : Type) [Field K] [IsAlgClosed K] (N δ m : ℕ) (g : MvPolynomial (Fin 1 × Fin N) K)
    (y : Fin m → Fin N → K), g.IsHomogeneous δ → NoSquare g → (∀ q, y q ≠ 0) →
    (∀ q q' (c : K), y q' = c • y q → q = q') →
    (∀ ξ : Fin N → K, eval (fun p => ξ p.2) g = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0) →
    m = δ ∧ ∃ c : K, c ≠ 0 ∧ g = C c * ∏ q, lin (y q) := by
  intro K _ _ N δ m g y hg hns hy hinj hz
  classical
  have hz' : ∀ x : Fin 1 × Fin N → K, eval x g = 0 ↔ ∃ q, eval x (lin (y q)) = 0 := by
    intro x
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz fun j => x (0, j)
    simp only [e] at h1
    simpa only [eval_lin] using h1
  have irr : ∀ q, Irreducible (lin (y q)) := fun q => irreducible_lin (hy q)
  have dvdg : ∀ q, lin (y q) ∣ g := fun q => by
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := lin (y q)) (b := g) fun x hx => (hz' x).2 ⟨q, hx⟩
    exact (irr q).prime.dvd_of_dvd_pow hn
  have nondvd : ∀ q q', q ≠ q' → ¬ lin (y q) ∣ lin (y q') := by
    intro q q' hne hd
    obtain ⟨a, ha⟩ := (irr q).associated_of_dvd (irr q') hd
    obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
    rw [ht, mul_comm] at ha
    refine hne (hinj q q' t (funext fun j => ?_))
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single ((0 : Fin 1), j) 1)) ha
    rw [coeff_C_mul, coeff_lin, coeff_lin] at h1
    simpa using h1.symm
  have Pdvd : (∏ q, lin (y q)) ∣ g := Finset.prod_dvd_of_isRelPrime
    (fun q _ q' _ hne => (irr q).isRelPrime_iff_not_dvd.2 (nondvd q q' hne)) fun q _ => dvdg q
  obtain ⟨h, hh⟩ := Pdvd
  have h0 : h ≠ 0 := fun e => hns.1 (by rw [hh, e, mul_zero])
  have hu : IsUnit h := by
    by_contra hu
    obtain ⟨p, pirr, pd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := g) (b := ∏ q, lin (y q)) fun x hx => by
      obtain ⟨q, hq⟩ := (hz' x).1 hx
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hq
    have pg : p ∣ g := hh ▸ pd.mul_left _
    obtain ⟨q, -, hq⟩ := (Prime.exists_mem_finset_dvd pirr.prime (pirr.prime.dvd_of_dvd_pow (pg.trans hn)))
    have hl : lin (y q) ∣ p := ((pirr.associated_of_dvd (irr q) hq).symm).dvd
    refine hns.2 (y q) (hy q) ?_
    rw [hh, pow_two]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (hl.trans pd)
  obtain ⟨c, hc, hcC⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hgC : g = C c * ∏ q, lin (y q) := by rw [hh, hcC, mul_comm]
  have hP : (∏ q, lin (y q)).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun q => lin (y q)) (fun _ => 1) fun q _ => isHomogeneous_lin (y q)
  have hgm : g.IsHomogeneous m := by
    rw [hgC]
    simpa using (isHomogeneous_C (Fin 1 × Fin N) c).mul hP
  exact ⟨(hgm.totalDegree hns.1).symm.trans (hg.totalDegree hns.1), c, hc.ne_zero, hgC⟩

end GlobalTheory.HSChoice.HyperplaneFactor
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.HSChoice.EtaleSection

theorem exists_eq_isoSpec_comp {k : Type} [CommRing k] {X : Scheme.{0}} [IsAffine X] (g : X ⟶ Spec (.of k)) :
    letI := algebraΓOfHom g
    ∃ a : CommRingCat.of k ⟶ Γ(X, ⊤), a.hom = algebraMap k Γ(X, ⊤) ∧ g = X.isoSpec.hom ≫ Spec.map a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop, rfl, ?_⟩
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem natCard_subPts {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I)
    (Ω : Type) [Field Ω] [Algebra k Ω] :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Nat.card (S.subPts I Ω) = Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have e1 : Nat.card (S.subPts I Ω) =
      Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun z => (⟨⟨z.1 ≫ I.subschemeι, by rw [Category.assoc]; exact z.2⟩,
      z.1, rfl⟩ : S.subPts I Ω)) ⟨?_, ?_⟩)).symm
    · intro z z' h
      apply Subtype.ext
      have h0 : z.1 ≫ I.subschemeι = z'.1 ≫ I.subschemeι := congrArg (fun x : S.subPts I Ω => x.1.1) h
      exact (cancel_mono I.subschemeι).1 h0
    · rintro ⟨x, z, hz⟩
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [← Category.assoc, hz]
        exact x.2
      · apply Subtype.ext
        apply Subtype.ext
        exact hz
  have hmk : ∀ φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv) ≫ I.subschemeι ≫ S.str =
        spMap (algebraMap k Ω) := by
    intro φ
    rw [he, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [ha]
    exact φ.commutes r
  have e2 : Nat.card {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)} =
      Nat.card (Γ(I.subscheme, ⊤) →ₐ[k] Ω) := by
    refine (Nat.card_congr (Equiv.ofBijective (fun φ : Γ(I.subscheme, ⊤) →ₐ[k] Ω =>
      (⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ I.subscheme.isoSpec.inv, hmk φ⟩ :
        {z : Sp Ω ⟶ I.subscheme // z ≫ I.subschemeι ≫ S.str = spMap (algebraMap k Ω)})) ⟨?_, ?_⟩)).symm
    · intro φ ψ h
      simp only [Subtype.mk.injEq, cancel_mono] at h
      have h2 := Spec.map_injective h
      ext r
      exact congrArg (fun f => f.hom r) h2
    · rintro ⟨z, hz⟩
      have hψ : Spec.map (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)) = z ≫ I.subscheme.isoSpec.hom :=
        Spec.map_preimage _
      have hc : a ≫ Spec.preimage (z ≫ I.subscheme.isoSpec.hom) = CommRingCat.ofHom (algebraMap k Ω) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ, Category.assoc, ← he]
        exact hz
      refine ⟨AlgHom.mk (Spec.preimage (z ≫ I.subscheme.isoSpec.hom)).hom (fun r => ?_), ?_⟩
      · have h3 := congrArg (fun f => f.hom r) hc
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, ha] at h3
        exact h3
      · apply Subtype.ext
        rw [Iso.comp_inv_eq]
        exact hψ
  rw [e1, e2]

theorem etale_of_algebraEtale {k : Type} [Field k] (S : LinSys k) (I : S.Y.IdealSheafData) (hI : S.IsFiniteSub I) :
    letI := algebraΓOfHom (I.subschemeι ≫ S.str)
    Algebra.Etale k Γ(I.subscheme, ⊤) → Etale (I.subschemeι ≫ S.str) := by
  letI := algebraΓOfHom (I.subschemeι ≫ S.str)
  intro h
  haveI : IsFinite (I.subschemeι ≫ S.str) := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ S.str)
  obtain ⟨a, ha, he⟩ := exists_eq_isoSpec_comp (I.subschemeι ≫ S.str)
  have h2 : Etale (Spec.map a) := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    rw [ha]
    exact (RingHom.etale_algebraMap (R := k) (S := Γ(I.subscheme, ⊤))).mpr h
  rw [he]
  infer_instance

theorem finite_finrank {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (E : Type) [Field E]
    [Algebra F E] (s : Fin T.D → Fin T.N → E)
    (hfin : ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite) :
    (T.toLinSys.baseChange E).IsFiniteSub (T.linSection E s) ∧
    (letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
    Module.Finite E Γ((T.linSection E s).subscheme, ⊤) ∧
      (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = T.del) := by
  have hv : (T.toLinSys.baseChange E).IsVariety := hT.alg.variety.baseChange E
  have H := GlobalTheory.ProperCut.topSelf_eq_length_of_smooth (T.toLinSys.baseChange E).str hv.smooth hv.proj
    (T.toLinSys.baseChange E).isLB (fun i => (T.toLinSys.baseChange E).comb (s i)) hfin
  have hdel : (T.toLinSys.baseChange E).del = T.del :=
    GlobalTheory.FieldChangeInter.del_baseChange F E T.toLinSys hT.alg.variety.proj
  refine ⟨H.1, ?_⟩
  refine ⟨H.2.2.2.2.1, ?_⟩
  rw [← hdel]
  exact H.2.2.2.2.2.symm

private lemma isHomogeneous_join_C_X {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (v : Fin (D + 1) × Fin N) :
    (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v).IsHomogeneous
      (if v.1 = Fin.last D then 1 else 0) := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simpa [join, Fin.castSucc_ne_last] using isHomogeneous_C (Fin 1 × Fin N) (s i j)
  · simpa [join] using isHomogeneous_X K ((0 : Fin 1), j)

theorem isHomogeneous_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N δ : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f) :
    (spec s f).IsHomogeneous δ := by
  classical
  unfold spec

  rw [f.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro m hm
  have hprod : (m.prod fun v e =>
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) ^ e).IsHomogeneous
      (∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v) :=
    IsHomogeneous.prod _ _ _ fun v _ => (isHomogeneous_join_C_X s v).pow (m v)
  have hdeg : ∑ v ∈ m.support, (if v.1 = Fin.last D then 1 else 0) * m v = δ := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv])]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa using hf m hm (Fin.last D)
    · intro i _ hi
      simp [hi]
    · simp
  have h2 := (isHomogeneous_C (Fin 1 × Fin N) (algebraMap F K (AddMonoidAlgebra.coeff f m))).mul hprod
  rw [zero_add, hdeg] at h2
  rw [aeval_monomial, MvPolynomial.algebraMap_apply]
  exact h2

private lemma eval_join_C_X_eq_join {K : Type} [CommRing K] {D N : ℕ} (s : Fin D → Fin N → K) (ξ : Fin N → K)
    (v : Fin (D + 1) × Fin N) :
    eval (fun p : Fin 1 × Fin N => ξ p.2)
      (join (fun i j => (C (s i j) : MvPolynomial (Fin 1 × Fin N) K)) (fun j => X ((0 : Fin 1), j)) v) = join s ξ v := by
  obtain ⟨i, j⟩ := v
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · simp [join]
  · simp [join]

theorem eval_spec {F K : Type} [CommRing F] [CommRing K] [Algebra F K] {D N : ℕ} (s : Fin D → Fin N → K)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (ξ : Fin N → K) :
    eval (fun p => ξ p.2) (spec s f) = aeval (join s ξ) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [spec, MvPolynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [spec, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [spec, map_mul, aeval_X] at hp ⊢
    rw [hp, eval_join_C_X_eq_join]

end GlobalTheory.HSChoice.EtaleSection
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanVal.value_tangent | exact GlobalTheory.MBLow.TanVal.value_tangent | (intros; apply GlobalTheory.MBLow.TanVal.value_tangent <;> assumption)
end
