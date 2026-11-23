module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import GroundTheory.Brauer.Bundle002
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle518
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Congr
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_smul_eq_of_eigvec_of_charpoly_separable {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g.charpoly.Separable) {μ : ℂ} {x y : Fin n → ℂ} (hx0 : x ≠ 0)
    (hx : g *ᵥ x = μ • x) (hy : g *ᵥ y = μ • y) : ∃ c : ℂ, y = c • x := by
  set f := Matrix.toLin' g
  have hc : f.charpoly = g.charpoly := Matrix.charpoly_toLin' g
  have h1 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, hc]
    exact Polynomial.rootMultiplicity_le_one_of_separable hg μ
  have mem : ∀ v : Fin n → ℂ, g *ᵥ v = μ • v → v ∈ Module.End.maxGenEigenspace f μ := fun v hv => by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨1, by simp [f, hv]⟩
  have h2 : Module.finrank ℂ (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
    (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, mem x hx⟩, fun h => hx0 (congrArg Subtype.val h)⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨x, mem x hx⟩ : Module.End.maxGenEigenspace f μ)
    fun h => hx0 (congrArg Subtype.val h)).1 h2 ⟨y, mem y hy⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem form_conjTranspose_mul_mul {n : ℕ} (A g : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    star u ⬝ᵥ (gᴴ * A * g) *ᵥ v = star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eigvec_pos_unique_of_similitude : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian),
    A.det ≠ 0 → sigPosH hA = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s →
    gᴴ * A * g = (s : ℂ) • A → g.charpoly.Separable → ∀ x y : Fin n → ℂ,
    0 < (star x ⬝ᵥ A *ᵥ x).re → 0 < (star y ⬝ᵥ A *ᵥ y).re →
    (∃ μ : ℂ, g *ᵥ x = μ • x) → (∃ ν : ℂ, g *ᵥ y = ν • y) → ∃ c : ℂ, y = c • x := by
  intro n A hA hdet hsig g s hs hsim hsep x y hxp hyp ⟨μ, hμ⟩ ⟨ν, hν⟩
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxp
  have hy0 : y ≠ 0 := by rintro rfl; simp at hyp
  have Q : ∀ u v : Fin n → ℂ, star (g *ᵥ u) ⬝ᵥ A *ᵥ (g *ᵥ v) = (s : ℂ) * (star u ⬝ᵥ A *ᵥ v) := by
    intro u v
    rw [← form_conjTranspose_mul_mul, hsim]
    have e : ((s : ℂ) • A) *ᵥ v = (s : ℂ) • (A *ᵥ v) := by
      exact Matrix.smul_mulVec (s : ℂ) A v
    rw [e, dotProduct_smul, smul_eq_mul]
  have scal : ∀ (a b : ℂ) (u v : Fin n → ℂ), star (a • u) ⬝ᵥ A *ᵥ (b • v) = star a * b * (star u ⬝ᵥ A *ᵥ v) := by
    intro a b u v
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]; ring
  have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hxp; simp at hxp
  have hQy : star y ⬝ᵥ A *ᵥ y ≠ 0 := fun h => by rw [h] at hyp; simp at hyp
  have eμ : star μ * μ = (s : ℂ) := by
    have := Q x x; rw [hμ, scal] at this; exact mul_right_cancel₀ hQx this
  have eν : star ν * ν = (s : ℂ) := by
    have := Q y y; rw [hν, scal] at this; exact mul_right_cancel₀ hQy this
  have exy : (star μ * ν - s) * (star x ⬝ᵥ A *ᵥ y) = 0 := by
    have := Q x y; rw [hμ, hν, scal] at this; rw [sub_mul, this, sub_self]
  by_cases hμν : μ = ν
  · subst hμν
    exact exists_smul_eq_of_eigvec_of_charpoly_separable hsep hx0 hμ hν
  · exfalso
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hμ0 : star μ ≠ 0 := fun h => hs0 (by rw [← eμ, h, zero_mul])
    have hne : star μ * ν - s ≠ 0 := by
      intro h
      apply hμν
      have : star μ * ν = star μ * μ := by rw [eμ]; exact sub_eq_zero.1 h
      exact (mul_left_cancel₀ hμ0 this).symm
    have horth : star x ⬝ᵥ A *ᵥ y = 0 := (mul_eq_zero.1 exy).resolve_left hne
    have := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig x y hxp horth hy0
    linarith

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFinOver

theorem liesOver_comp_complexConj_of_not_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p)
    (ψ : G.F →+* PadicAlgCl p), ¬ LiesOver G.Kq G.u ψ →
      LiesOver G.Kq G.u (ψ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  intro p _ G ψ h x
  exact (GlobalTheory.HTGroupOver.liesOver_or_conj p G ψ).resolve_left h x

end GlobalTheory.StabFinOver
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.ClsReg

theorem eq_zero_of_commute_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.C),
    (minpoly G.F y₀).Separable →
    (minpoly G.F y₀).natDegree = G.n → ∀ x : G.C, Commute x y₀ → ∀ k : ℕ, x ^ k = 0 → x = 0 := by
  intro p _ G y₀ hsep hdeg x hx k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  ·
    have h10 : (1 : G.C) = 0 := by simpa using hk
    rw [← one_mul x, h10, zero_mul]
  have hk0 : k ≠ 0 := hkpos.ne'
  have hc := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC y₀ hsep hdeg
  have hxmem : x ∈ Subalgebra.centralizer G.F ({y₀} : Set G.C) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hx.eq.symm
  rw [hc, Algebra.adjoin_singleton_eq_range_aeval] at hxmem
  obtain ⟨f, rfl⟩ := hxmem
  have h1 : Polynomial.aeval y₀ (f ^ k) = 0 := by
    rw [map_pow]; exact hk
  have h2 : minpoly G.F y₀ ∣ f ^ k := minpoly.dvd G.F y₀ h1
  have hsq : Squarefree (minpoly G.F y₀) := hsep.squarefree
  have h3 : minpoly G.F y₀ ∣ f := (hsq.dvd_pow_iff_dvd hk0).1 h2
  obtain ⟨g, hg⟩ := h3
  show Polynomial.aeval y₀ f = 0
  rw [hg, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.LKCx.ClsReg
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  first | (exact @GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (exact GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (intros; apply GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.SigCong

theorem card_pos_le_of_conj {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hX : Xᴴ * A * X = B) :
    Fintype.card {i : Fin n // 0 < hB.eigenvalues i} ≤ Fintype.card {i : Fin n // 0 < hA.eigenvalues i} := by
  set φ : ({i // 0 < hB.eigenvalues i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
      GlobalTheory.SimSign.extZero (fun i => 0 < hB.eigenvalues i) with hφ
  have hq : ∀ w, w ≠ 0 → 0 < (star (φ w) ⬝ᵥ A *ᵥ φ w).re := fun w hw => by
    simp only [hφ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [GlobalTheory.SimSign.quad_mulVec, hX, GlobalTheory.SimSign.re_quad_ext]
    exact GlobalTheory.SimSign.sum_pos B hB w hw
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hq w hne
    rw [hw] at this
    simp at this
  have hS : ∀ u ∈ LinearMap.range φ, u ≠ 0 → 0 < (star u ⬝ᵥ A *ᵥ u).re := by
    rintro u ⟨w, rfl⟩ hu
    exact hq w (fun h0 => hu (by rw [h0, map_zero]))
  have h1 := GlobalTheory.SimSign.finrank_le_pos A hA _ hS
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

theorem sigPosH_congr : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 →
    ∀ (Z : GL (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian),
      B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) → sigPosH hB = sigPosH hA := by
  intro n A hA _ Z B hB hBZ
  unfold sigPosH
  refine le_antisymm (card_pos_le_of_conj A B _ hA hB hBZ.symm)
    (card_pos_le_of_conj B A ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) hB hA ?_)
  have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv Z
  rw [hBZ]
  calc (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * A *
        ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1]; simp

end GlobalTheory.SigCong
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CentIrr

noncomputable def rootHom (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    AdjoinRoot (minpoly F y) →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {minpoly F y}) (Polynomial.aeval y) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, minpoly.aeval, zero_mul])

theorem rootHom_root (F C : Type) [Field F] [Ring C] [Algebra F C] (y : C) :
    rootHom F C y (AdjoinRoot.root (minpoly F y)) = y := by
  exact Polynomial.aeval_X y

theorem commute_iff_mem_adjoin (F C : Type) [Field F] [Ring C] [Algebra F C] [FiniteDimensional F C]
    [Algebra.IsCentral F C] [IsSimpleRing C] (n : ℕ) (hn : 0 < n) (hC : Module.finrank F C = n ^ 2)
    (y : C) (hirr : Irreducible (minpoly F y)) (hdeg : (minpoly F y).natDegree = n) (z : C) :
    Commute z y ↔ z ∈ Algebra.adjoin F ({y} : Set C) := by
  set B := Algebra.adjoin F ({y} : Set C) with hBdef
  have hcommB : ∀ {u v : C}, u ∈ B → v ∈ B → u * v = v * u := by
    intro u v hu hv
    have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hu
    rw [Subalgebra.mem_centralizer_iff] at this
    apply (this v _).symm
    refine Algebra.adjoin_le ?_ hv
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
  haveI : Fact (Irreducible (minpoly F y)) := ⟨hirr⟩
  set j : AdjoinRoot (minpoly F y) →ₐ[F] C := rootHom F C y
  have hj : Function.Injective j := j.toRingHom.injective
  have hrange : j.range = B := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  have hne : minpoly F y ≠ 0 := hirr.ne_zero
  have hEdim : Module.finrank F (AdjoinRoot (minpoly F y)) = n := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let eB : AdjoinRoot (minpoly F y) ≃ₐ[F] B := (AlgEquiv.ofInjective j hj).trans (Subalgebra.equivOfEq _ _ hrange)
  haveI : IsSimpleRing B := IsSimpleRing.of_ringEquiv eB.toRingEquiv inferInstance
  have hBdim : Module.finrank F B = n := by rw [← eB.toLinearEquiv.finrank_eq, hEdim]
  set Z := Subalgebra.centralizer F (B : Set C)
  have hBZ : B ≤ Z := by
    intro a ha
    rw [Subalgebra.mem_centralizer_iff]
    intro b hb
    exact hcommB hb ha
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_centralizer (K := F) (A := C) B
  have hdim : Module.finrank F B = Module.finrank F Z := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Module.finrank F B by rw [hBdim]; exact hn)
    rw [h1, hC, hBdim, sq]
  have hEq : B = Z := Subalgebra.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hBZ) hdim)
  constructor
  · intro hz
    have hzZ : z ∈ Z := by
      rw [Subalgebra.mem_centralizer_iff]
      intro b hb
      have := Algebra.adjoin_le_centralizer_centralizer F ({y} : Set C) hb
      rw [Subalgebra.mem_centralizer_iff] at this
      refine (this z ?_).symm
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]; exact hz.eq.symm
    rw [hEq]; exact hzZ
  · intro hz
    exact (hcommB hz (Algebra.self_mem_adjoin_singleton F y) : _)

theorem centralizer_unit_eq_field : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (y₀ : G.Cˣ),
    Irreducible (minpoly G.F (y₀ : G.C)) → (minpoly G.F (y₀ : G.C)).natDegree = G.n →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra G.F E) (j : E →ₐ[G.F] G.C),
      Function.Injective j ∧ ∀ z : G.C, Commute z (y₀ : G.C) ↔ ∃ e, j e = z := by
  intro p _ G y₀ hirr hdeg
  haveI : Fact (Irreducible (minpoly G.F (y₀ : G.C))) := ⟨hirr⟩
  let j : AdjoinRoot (minpoly G.F (y₀ : G.C)) →ₐ[G.F] G.C := rootHom G.F G.C (y₀ : G.C)
  have hne : minpoly G.F (y₀ : G.C) ≠ 0 := hirr.ne_zero
  haveI : FiniteDimensional G.F (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    (AdjoinRoot.powerBasis hne).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    Module.Finite.trans G.F _
  haveI : CharZero (AdjoinRoot (minpoly G.F (y₀ : G.C))) :=
    charZero_of_injective_algebraMap (algebraMap G.F _).injective
  haveI : NumberField (AdjoinRoot (minpoly G.F (y₀ : G.C))) := ⟨⟩
  have hrange : j.range = Algebra.adjoin G.F ({(y₀ : G.C)} : Set G.C) := by
    rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton]
    rw [rootHom_root]
  refine ⟨AdjoinRoot (minpoly G.F (y₀ : G.C)), inferInstance, inferInstance, inferInstance, j,
    j.toRingHom.injective, fun z => ?_⟩
  rw [commute_iff_mem_adjoin G.F G.C G.n G.n_pos G.rankC _ hirr hdeg z, ← hrange]
  rfl

end GlobalTheory.CentIrr
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid Formalism.L2.Host

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}

theorem natCast_mem_of_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal) : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal := h
  rwa [map_natCast] at h1

theorem natCast_mem_under {w : HeightOneSpectrum (𝓞 D.host.E)} {p : ℕ}
    (h : ((p : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : ((p : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
  show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ w.asIdeal
  rwa [map_natCast]

theorem nFun_add_one_lt_eExp_add_cen (C : ℝ) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (cen D C (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := GlobalTheory.LamTie.e_add_v_two_pos (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0 j
  have h2 := Int.lt_floor_add_one
    ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid (a.1 + 1))
  have h3 := (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).a (a.1 + 1) =
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := rfl
  have h5 : ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc (D.eTau.symm g)) (sLen D) (gap D C) 0).ga : ℚ) = gap D C := rfl
  have h6 := (isLeast_gap D C).1.2.1
  have h7 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((bigN D + 2 : ℕ) : ℚ) ≤ gap D C := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ gap D C := by positivity
  have h11 : (gap D C : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (gap D C : ℚ) := by nlinarith
  have h12 : BlochKatoReduction.Gen.NFun D.R = bigN D := GlobalTheory.LamTie.nFun_eq_bigN D
  rw [h12]
  unfold eExp cen
  push_cast at h8
  linarith

end GlobalTheory.BigTop.Fun

end
end

section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.ringKrullDim_cone_image_of_birational_linearSystem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  first | exact @GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | exact GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational | (intros; apply GlobalTheory.Adelic.ConeDim.ringKrullDim_imageIdeal_of_birational <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  first | exact @GlobalTheory.Obs.unobDim_of_formSt | exact GlobalTheory.Obs.unobDim_of_formSt | (intros; apply GlobalTheory.Obs.unobDim_of_formSt <;> assumption)
end
