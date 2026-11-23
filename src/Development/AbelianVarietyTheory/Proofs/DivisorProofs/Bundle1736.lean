module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolic
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle831
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.HeckeUnif

open GlobalTheory.TangentOrigin

theorem existsUnique_linear_lift_of_hom :
    ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
      SmoothOfRelativeDimension g G.hom → ∀ (y : Sp ℂ ⟶ X) (e' : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (β : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e' → (∀ z w, β (z + w) = β z * β w) →
      IsHolTo Set.univ (fun z => (β z).left) → ∃! M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (M z) = β z := by
  intro X G _ _ g hab hsm y e' β he' hβ hholG
  obtain ⟨Λ, hdisc, -, hker⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hab hsm y e' he'
  letI : CommGroup (Over.mk y ⟶ G) := inferInstance
  let ex : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (e' z)) he'.1
  let G' : (Fin g → ℂ) →+ Additive (Over.mk y ⟶ G) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (β z)) hβ
  let pt : (Over.mk y).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (Over.mk y).left, q = pt := fun q ↦ Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (e' 0).left pt) (U := ⊤) (Set.mem_univ _)
  have h0 : ⊤ ≤ (e' 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker' : (ex.ker : Set (Fin g → ℂ)) = Λ := Set.ext fun z ↦ hker z
  have hS0 : (0 : Additive (Over.mk y ⟶ G)) ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U} := by
    rw [← map_zero ex]
    exact h0
  have hsep : ∀ a ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      ∀ b ∈ {a : Additive (Over.mk y ⟶ G) | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U},
      (∀ s : Γ(G.left, U), valAt' (Additive.toMul a).left U s = valAt' (Additive.toMul b).left U s) → a = b := by
    intro a ha b hb h
    exact Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦
        (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))))
  have hSe : IsOpen {z : Fin g → ℂ | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    have := (he'.2.2.1 U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hSG : IsOpen {z : Fin g → ℂ | ⊤ ≤ (β z).left ⁻¹ᵁ U} := by
    have := (hholG U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfe : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (e' z).left U s) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ U} := by
    intro s
    have := (he'.2.2.1 U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hfG : ∀ s : Γ(G.left, U), DifferentiableOn ℂ (fun z ↦ valAt' (β z).left U s)
      {z | ⊤ ≤ (β z).left ⁻¹ᵁ U} := by
    intro s
    have := (hholG U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  have hD : ∀ w : Fin g → ℂ, (∀ s : Γ(G.left, U), fderiv ℂ (fun z ↦ valAt' (e' z).left U s) 0 w = 0) → w = 0 := by
    intro w hw
    obtain ⟨v, hv, -⟩ := he'.2.2.2.1 w
    obtain ⟨v0, hv0, -⟩ := he'.2.2.2.1 0
    have hvU : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff v.left U).2 (hv.1 ▸ h0)
    have hv0U : ⊤ ≤ v0.left ⁻¹ᵁ U := (top_le_preimage_iff v0.left U).2 (hv0.1 ▸ h0)
    have key : ∀ (u : Sp (DualNumber ℂ) ⟶ G.left) (hu : ⊤ ≤ u ⁻¹ᵁ U) (x : Sp ℂ ⟶ G.left) (hx : ⊤ ≤ x ⁻¹ᵁ U)
        (s : Γ(G.left, U)), spMap fstC ≫ u = x → (evalPt u U hu s).fst = evalPt x U hx s := by
      rintro u hu x hx s rfl
      exact (evalPt_spMap_comp fstC u U hu hx s).symm
    have heq : v.left = v0.left := by
      refine ext_evalPt (R := DualNumber ℂ) hU hvU hv0U (RingHom.ext fun s ↦ TrivSqZeroExt.ext ?_ ?_)
      · exact (key _ hvU _ h0 s hv.1).trans (key _ hv0U _ h0 s hv0.1).symm
      · have a := hv.2 U hvU s
        have b := hv0.2 U hv0U s
        rw [map_zero] at b
        exact a.trans ((hw s).trans b.symm)
    have hv0' : IsDerivAt0 (fun z ↦ (e' z).left) w v0.left := heq ▸ hv
    exact (he'.2.2.2.2 v0 hv0.1).unique hv0' hv0
  obtain ⟨F, hF, hu⟩ := GlobalTheory.existsUnique_linear_lift_of_separating (ex := ex) (G := G') he'.2.1
    (hker' ▸ isDiscrete_iff_discreteTopology.2 hdisc)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(G.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    hS0 hsep hSe hSG hfe hfG hD
  exact ⟨F, hF, fun M hM ↦ hu M hM⟩

theorem eq_zero_of_real_smul_mem {g : ℕ} (A : AddSubgroup (Fin g → ℂ)) (hA : DiscreteTopology A) (z : Fin g → ℂ)
    (hz : ∀ r : ℝ, (r : ℂ) • z ∈ A) : z = 0 := by
  by_contra hne
  have hopen : IsOpen ({⟨0, A.zero_mem⟩} : Set A) := isOpen_discrete _
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.mp hopen
  have h0U : (0 : Fin g → ℂ) ∈ U := by
    have : (⟨0, A.zero_mem⟩ : A) ∈ Subtype.val ⁻¹' U := by rw [hUe]; rfl
    exact this
  have hc : Continuous (fun r : ℝ => (r : ℂ) • z) := by fun_prop
  have hV : IsOpen ((fun r : ℝ => (r : ℂ) • z) ⁻¹' U) := hU.preimage hc
  have h0 : (0 : ℝ) ∈ (fun r : ℝ => (r : ℂ) • z) ⁻¹' U := by simpa using h0U
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  have hr : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hmem : (⟨((ε / 2 : ℝ) : ℂ) • z, hz _⟩ : A) ∈ Subtype.val ⁻¹' U := hball hr
  rw [hUe] at hmem
  have h2 : ((ε / 2 : ℝ) : ℂ) • z = 0 := congrArg Subtype.val hmem
  rcases smul_eq_zero.mp h2 with h | h
  · have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h
    linarith
  · exact hne h

end GlobalTheory.HeckeUnif

namespace GlobalTheory.UPel.HT.Hecke

open GlobalTheory.UnifPull GlobalTheory.HeckeUnif

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

end GlobalTheory.UPel.HT.Hecke
end
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.isogenous_pDivGroup_finrank_omega_dual :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
      IsIsog q → Function.Injective (T.map q) ∧
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
        Module.finrank k G.omega = Module.finrank k H.omega ∧
        Module.finrank k G.dual.omega = Module.finrank k H.dual.omega :=
  @GlobalTheory.Dieu.isog_finrank_omega
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthHtOne

open Module

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem le_finrank_coker_omegaMap [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h1 : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1))
    (he : HasLogDeg q e) : e ≤ finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  unfold HasLogDeg at he
  obtain ⟨N, hN⟩ := he
  have hlev : finrank k (G.A 1 ⧸ kerIdeal (q.app 1)) = p ^ e := by
    rw [← GlobalTheory.Dieu.finrank_quot_kerIdeal_eq p k G H 1 (max N 1) q q' (by rw [pow_one]; exact h1)
      (le_max_right _ _)]
    exact hN _ (le_max_left _ _)
  obtain ⟨C, _, _, _, _, π, hπ, hker, hnil, hFaug⟩ := GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel p k G H q
  have hker' : RingHom.ker π = kerIdeal (q.app 1) := by rw [hker]; exact sup_eq_left.2 hF
  have hC : finrank k C = p ^ e := by
    rw [← hlev, ← hker']
    exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (π : G.A 1 →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq).symm
  have hfrobC : frobKerIdeal p k C = ⊥ := by
    rw [eq_bot_iff]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hnil a ha]
  have hCq : finrank k C = finrank k (C ⧸ frobKerIdeal p k C) := by
    refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k (frobKerIdeal p k C)).toLinearMap
      ⟨fun a b h => ?_, Ideal.Quotient.mkₐ_surjective k _⟩)
    have h' := Ideal.Quotient.eq.1 h
    rwa [hfrobC, Ideal.mem_bot, sub_eq_zero] at h'
  have hle := GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p k C
  rw [← hCq, hC] at hle
  have hcot := (GlobalTheory.T.cotangent_kernel_eq_coker_omegaMap p k G H q C π hπ).2.1 (by rw [hker]; exact sup_le_sup_left hFaug _) hker'.ge
  rw [hcot]
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

theorem finrank_coker_lieMap {A B : PDivGroup p k} (f : A ⟶ B) [FiniteDimensional k A.omega]
    [FiniteDimensional k B.omega] (hd : finrank k A.omega = finrank k B.omega) :
    finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) =
      finrank k (A.omega ⧸ LinearMap.range (omegaMap A B f)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range (lieMap A B f))
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (omegaMap A B f))
  have h3 : finrank k (LinearMap.range (lieMap A B f)) = finrank k (LinearMap.range (omegaMap A B f)) :=
    LinearMap.finrank_range_dualMap_eq_finrank_range (omegaMap A B f)
  have h4 : finrank k B.Lie = finrank k B.omega := Subspace.dual_finrank_eq
  omega

theorem finrank_coker_lieMap_congr {A B A' B' : PDivGroup p k} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B)
    (f' : A' ⟶ B') (hc : eA.hom ≫ f' = f ≫ eB.hom) :
    finrank k (B'.Lie ⧸ LinearMap.range (lieMap A' B' f')) =
      finrank k (B.Lie ⧸ LinearMap.range (lieMap A B f)) := by
  let L : B.Lie ≃ₗ[k] B'.Lie := LinearEquiv.ofLinear (lieMap B B' eB.hom) (lieMap B' B eB.inv)
    (by rw [← lieMap_comp, eB.inv_hom_id, lieMap_id]) (by rw [← lieMap_comp, eB.hom_inv_id, lieMap_id])
  have hA : LinearMap.range (lieMap A A' eA.hom) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x => ⟨lieMap A' A eA.inv x, ?_⟩
    rw [← LinearMap.comp_apply, ← lieMap_comp, eA.inv_hom_id, lieMap_id, LinearMap.id_apply]
  have hr : LinearMap.range (lieMap A' B' f') = (LinearMap.range (lieMap A B f)).map (L : B.Lie →ₗ[k] B'.Lie) := by
    rw [← LinearMap.range_comp_of_range_eq_top _ hA, ← lieMap_comp, hc, lieMap_comp, LinearMap.range_comp]
    rfl
  rw [hr]
  exact (Submodule.Quotient.equiv _ _ L rfl).finrank_eq.symm

end GlobalTheory.Dieu.ColengthHtOne


open GlobalTheory.Dieu.ColengthHtOne in
theorem GlobalTheory.Dieu.le_colength_of_htOne : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ), q ≫ q' = (p : ℤ_[p]) • 𝟙 G →
    q' ≫ q = (p : ℤ_[p]) • 𝟙 H → frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1) → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
    e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) := by
  intro p _ T k _ _ _ G H q q' e h1 h2 hF he
  have h3 := le_finrank_coker_omegaMap G H q q' e h1 hF he
  have hp0 : (p : k) = 0 := CharP.cast_eq_zero k p
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 G
  haveI := GlobalTheory.PDivGroup.finite_omega_of_eq_zero hp0 H
  have hiso : IsIsog q := by
    unfold IsIsog
    exact ⟨1, q', by simpa only [pow_one] using h1, by simpa only [pow_one] using h2⟩
  have hd := (GlobalTheory.Dieu.isog_finrank_omega p T k G H q hiso).2.2.1
  have hL := (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k H.dual G.dual (dualHom G H q)).2
  rw [finrank_coker_lieMap_congr G.bidual H.bidual q _ (bidual_hom_dualHom_dualHom q),
    finrank_coker_lieMap q hd] at hL
  refine ⟨le_trans (by exact_mod_cast h3) (GlobalTheory.T.finrank_quot_range_le_length_quot_range_map p T k G H q).1, le_trans (by exact_mod_cast h3) hL, h3⟩
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (β f : GL (Fin (m + 1)) (Cinf E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, β (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * β y) → (∃ B : Lie E (m + 1) → ℂ, ContDiffOn ℝ ∞ B (invSet E (m + 1)) ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), B (toL y.val) = β y) → (∃ C : Set (GL (Fin (m + 1)) (Cinf E)), IsCompact C ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, β y ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), u⁻¹ * y ∈ C) → (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, f (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * f y) → Continuous f → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) → f 1 ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, ∫ x, k x * f (y * γ x) ∂ν = β y := by
  first | exact @GlobalTheory.JSW.MirCinf.kirillov_cinf | exact GlobalTheory.JSW.MirCinf.kirillov_cinf | (intros; apply GlobalTheory.JSW.MirCinf.kirillov_cinf <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

noncomputable section

namespace GlobalTheory.JSW.NzSph

theorem finite_bad (E : Type) [Field E] [NumberField E] (a : ℕ) (k : GL (Fin a) (Af E)) :
    {w : HeightOneSpectrum (𝓞 E) | GeneralLinearGroup.map (pLoc E w) k ∉ KGL w (n := a)}.Finite :=
  GlobalTheory.T.finiteAdelicGL_mem_integral_cofinite_places E a k

theorem exists_outside (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (k : GL (Fin a) (Af E)) : ∃ k' : GL (Fin a) (Af E),
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧
      ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 :=
  GlobalTheory.T.exists_finiteAdelicGL_agree_outside_trivial_on_finset E a S k

theorem local_decomp (E : Type) [Field E] [NumberField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) :
    ∃ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin a), ∃ (N : ℕ) (l : Fin a → ℕ), ∃ k ∈ KGL w (n := a),
      g = u * GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ => N) * GlobalTheory.JSW.diagPow ϖ l * k :=
  GlobalTheory.T.iwasawa_decomposition_adicCompletionGL_diagonalPowers E a w ϖ hϖ g

theorem act_fin_eq_of_outside (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (hφ : IsAutForm φ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) (k : GL (Fin a) (Af E))
    (hk : ∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a))
    (hk1 : ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) : act (.fin k) φ = φ :=
  GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed E a φ hφ S hS k hk hk1

end GlobalTheory.JSW.NzSph

namespace GlobalTheory.JSW.NzSph

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem map_pLoc_pFin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comp_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a h) = GeneralLinearGroup.map (pLoc E v) h := by
  rw [finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]

theorem diagPow_const_comm {K : Type} [CommRing K] {n : ℕ} (c : Kˣ) (N : ℕ) (h : GL (Fin n) K) :
    GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) * h = h * GlobalTheory.JSW.diagPow c (fun _ : Fin n => N) := by
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable [_root_.NumberField.IsTotallyComplex E]

theorem whit_act_fin (φ : Sm E a) (k : GL (Fin a) (Af E)) (y : GA E a) :
    whit (act (.fin k) φ).1 y = whit φ.1 (y * finGL E a k) := by
  rw [whit_mul_right]; rfl

theorem act_fin_mul (k k' : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin (k * k')) φ = act (.fin k) (act (.fin k') φ) := by
  show finRep E a (k * k') φ = finRep E a k (finRep E a k' φ)
  rw [map_mul]; rfl

theorem exists_whittaker_ne_zero_induction_bad_places (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hψ : ∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ)
    (hα : ∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ g : GA E a,
      (∀ w ∉ S, w ∉ T → GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g ∈ KGL w (n := a)) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, whit φ.1 x ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E a S (GeneralLinearGroup.map (pFin E) g)
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E a φ (π.cusp φ hφV).1 S hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E a k)⁻¹, fun w hw => ?_, ?_⟩
    · rw [map_mul, map_inv, comp_finGL, hk1 w hw, map_pLoc_pFin, mul_inv_cancel]
    · have e : g = g * (finGL E a k)⁻¹ * finGL E a k := by group
      rw [e, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w T hwT ih =>
    intro φ hφV hφ g hg hW
    by_cases hwS : w ∈ S
    · refine ih φ hφV hφ g (fun v hv hvT => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwS), hvT⟩
    obtain ⟨ϖ0, hϖ0⟩ := exists_isUnifV (E := E) w
    have hne : ϖ0 ≠ 0 := fun h => by simp [IsUnifV, h] at hϖ0
    let ϖ : (w.adicCompletion E)ˣ := Units.mk0 ϖ0 hne
    have hϖ : IsUnifV E w (ϖ : w.adicCompletion E) := hϖ0
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E a w ϖ hϖ gw
    let z := GlobalTheory.JSW.diagPow ϖ⁻¹ (fun _ : Fin a => N)
    let d := GlobalTheory.JSW.diagPow ϖ l
    let F : GL (Fin a) (w.adicCompletion E) →* GA E a := (finGL E a).comp (locGL E a w)
    have hF : ∀ h, F h = finGL E a (locGL E a w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E a (locGL E a w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E a γ = ratGL E a γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwS k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E a w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ S, ∀ k' ∈ KGL v (n := a), act (.fin (locGL E a v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E a v k' * locGL E a w z = locGL E a w z * locGL E a v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E a w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2
    have h4 : whit φ₁.1 y ≠ 0 := by
      have := GlobalTheory.JSW.whit_mul_locGL_diagPow E a π w (α w) (hψ w hwS) (hα w hwS) φ₁ hφ₁V (hφ₁ w hwS) y hyw ϖ hϖ l
      rw [hF d] at h3
      rw [this] at h3
      exact right_ne_zero_of_mul h3
    refine ih φ₁ hφ₁V hφ₁ y (fun v hv hvT => ?_) h4
    by_cases hvw : v = w
    · subst hvw; rw [hyw]; exact one_mem _
    · rw [hyv v hvw]
      exact hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvT⟩)

theorem exists_sph_whit_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧ ∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0 := by
  intro E _ _ _ m S hψ π α hα
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π S (fun w => Finset.univ.val.map (α w)) hα
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) g)
  refine exists_whittaker_ne_zero_induction_bad_places S hψ π α hα hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwT => ?_) hg
  by_contra h
  refine hwT (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) ∉ KGL w (n := (m + 1))
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSph
end
end
