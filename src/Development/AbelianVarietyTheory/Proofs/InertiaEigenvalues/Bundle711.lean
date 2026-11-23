module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle693
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle694
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle683
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApprox
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle695
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.dividedUniformizerPower_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ q : ℕ, dFam a K e q ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.dFam_mem_goodSet | exact GlobalTheory.CrysPrism.dFam_mem_goodSet | (intros; apply GlobalTheory.CrysPrism.dFam_mem_goodSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mul_mem_crystallinePrismDividedPowerFamilies : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e := by
  first | exact @GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | exact GlobalTheory.CrysPrism.mul_mem_QSet_of_mem | (intros; apply GlobalTheory.CrysPrism.mul_mem_QSet_of_mem <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.dividedPowerFamily_single_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  first | exact @GlobalTheory.CrysPrism.ofW_single | exact GlobalTheory.CrysPrism.ofW_single | (intros; apply GlobalTheory.CrysPrism.ofW_single <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.dividedVariablePower_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → ∀ i : ℕ, xFam a K i ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet | exact GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → (∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂) → (∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0) → ∀ w : ℕ × ℕ → Wq l a, LTo0 l w → ∀ v b : ℕ × ℕ → Wq l a, frob2 φ₂ (ofW t K e w) = ofW t K e v → frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b → LTo0 l v ∧ LTo0 l b := by
  first | exact @GlobalTheory.CrysPrism.frob_keeps_decay | exact GlobalTheory.CrysPrism.frob_keeps_decay | (intros; apply GlobalTheory.CrysPrism.frob_keeps_decay <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.uniformizerFamily_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.uFam_mem_GoodSet | exact GlobalTheory.CrysPrism.uFam_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.uFam_mem_GoodSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.constantCoeffFamily_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ c : Wq l a, cstW t K c ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.cstW_mem_GoodSet | exact GlobalTheory.CrysPrism.cstW_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.cstW_mem_GoodSet <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)), ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H))) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) → ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.goodSet_of_finite_of_local | exact GlobalTheory.CrysPrism.goodSet_of_finite_of_local | (intros; apply GlobalTheory.CrysPrism.goodSet_of_finite_of_local <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_pow_mem_finiteSupportDoublePowerSeries : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0 := by
  first | exact @GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | exact GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero | (intros; apply GlobalTheory.CrysPrism.FinSupp.exists_coeff_frob2_ofW_and_pow_eq_zero <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.CrysDiag.eps_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro E jA hR hM oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ hκ Q _ c y hy τ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.crystal_basis_transport_free_over_prism l a e O K t ϖ ι P T I E jA hR hM oE hoE b hb
  have key : ∀ j, ∑ i, ∑ q, δ.f (y i j q) • (oE (c i j q)).u S₀ (E.tr (δ.comp p₀) (b i)) =
      ∑ i, ∑ _q : Unit, (if i = j then (1 : S₀.A) else 0) • (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) := by
    intro j
    have hfix : ∀ i, (oE 1).u S₀ (E.tr (δ.comp p₀) (b i)) = E.tr (δ.comp p₀) (b i) := fun i => by
      rw [(oE 1).u_tr, h1]
    simp only [hfix, ite_smul, one_smul, zero_smul, Finset.sum_const, Finset.card_univ, Fintype.card_unit]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    conv_rhs => rw [hδ, E.tr_comp, hy j]

    simp only [E.tr_comp, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
    rw [(oE (c i j q)).u_tr]
    exact ((E.tr δ).map_smulₛₗ _ _).symm
  have hC : ∀ w : Wq l a, (toAc t K (PowerSeries.C w) τ : K⟦X⟧) = PowerSeries.C (algebraMap O K (emb t τ w)) := by
    intro w
    ext n
    rw [coeff_toAc, PowerSeries.coeff_C, PowerSeries.coeff_C]
    split_ifs <;> simp
  have hψ : ∀ z : ℤ_[l], κ₀ τ ((δ.comp p₀).f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) =
      algebraMap O K⟦X⟧ (algebraMap ℤ_[l] O z) := by
    intro z
    change κ₀ τ (δ.f (p₀.f _)) = _
    rw [hκ₀, hκ, PowerSeries.algebraMap_apply, frobS_C, PowerSeries.constantCoeff_C, hC,
      AlgEquiv.commutes, AlgHom.commutes, PowerSeries.algebraMap_apply]
  refine Matrix.ext fun i j => ?_
  have hij := h2 S₀ (δ.comp p₀) Q Unit (fun i q => c i j q) (fun i q => δ.f (y i j q)) (fun _ _ => 1)
    (fun i _ => if i = j then (1 : S₀.A) else 0) (by simpa only [one_smul] using key j) K⟦X⟧ (κ₀ τ) hψ i
  simp only [hκ₀, Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, apply_ite (κ₀ τ),
    map_one, map_zero] at hij

  rw [Matrix.map_apply, Matrix.of_apply, map_sum, Matrix.one_apply, ← hij]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    PowerSeries.constantCoeff_C, PowerSeries.algebraMap_apply]
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

section Scal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem galOD_crisToOD (g : GQ l) (x : OCr l O) :
    galOD O g (crisToOD l O x) = crisToOD l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.crisP_unique_equivariant l (crisP l) (isCrisP_crisP l)).2.1 g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isUnit_natCast_OD {n : ℕ} (hn : n ≠ 0) : IsUnit (n : OD l O) := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (OD l O)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul (isUnit_l_OD.pow _)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]


variable (O K) in
theorem dvd_toOD_mu (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) :
    ϖ.iAl O K (EIn l e _) ∣ toOD l O (1 ⊗ₜ ϖ.mu g) := by
  have hξ : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  have hmem : ϖ.mu g ∈ Ideal.span {ϖ.ev 1 (eis l 1 e)} := by
    rw [ϖ.span_ev_eis 1]
    exact ϖ.theta_mu (ϖ.gal_pi a g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨1 ⊗ₜ ainfToBdRp l c, ?_⟩
  rw [hξ, ← hc]
  change (1 : O) ⊗ₜ[ℤ_[l]] ainfToBdRp l (c * _) = _
  rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]


variable (O) in
theorem crisToOD_muDiv (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    crisToOD l O (ϖ.muDiv a O g i) = toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) := by
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  have h2 := congrArg (crisToOD l O) h1
  rw [map_mul, map_natCast, map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, ← toOCr_tmul, crisToOD_toOCr] at h2
  have hu := isUnit_natCast_OD (l := l) (O := O) i.factorial_ne_zero
  rw [← h2, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl


variable (K) in
theorem taylor_S_mod (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (s : S O K e) (R : ℕ) :
    ϖ.iAl O K (EIn l e _) ^ R ∣ galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
  obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ R
  refine GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ R _ fun k => ?_
  obtain ⟨M₀, hM₀⟩ := ϖ.taylor_S a O K g s (N + k)
  obtain ⟨z, hz⟩ := hM₀ (max M₀ R) (le_max_left _ _)
  obtain ⟨y, hy⟩ := hN z
  refine ⟨y, ?_⟩
  have hz' := congrArg (crisToOD l O) hz

  simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, crisToOD_muDiv] at hz'
  rw [← galOD_crisToOD, ← Finset.sum_range_add_sum_Ico _ (le_max_right M₀ R)] at hz'
  have key : galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) - (l : OD l O) ^ k * toOD l O y =
      (l : OD l O) ^ k * ((l : OD l O) ^ N * crisToOD l O z - toOD l O y) +
        ∑ i ∈ Finset.Ico R (max M₀ R), toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    linear_combination hz'
  rw [key]
  refine dvd_add (Dvd.dvd.mul_left hy _) (Finset.dvd_sum fun i hi => ?_)
  have hi' : R ≤ i := (Finset.mem_Ico.1 hi).1
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ hi').trans
    (pow_dvd_pow_of_dvd (dvd_toOD_mu O K ϖ g) i)) _) _

end Scal

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

section Scal2

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] [CompleteSpace K]

theorem taylor_invL_mod (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {f : K⟦X⟧}
    (hf : f ∈ invL l (S O K e)) (R : ℕ) :
    galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i *
      Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f)) ∈
      Ideal.span {ϖ.iAl O K (EIn l e _) ^ R} := by
  have hiHat : ∀ (f' : K⟦X⟧) (hf' : f' ∈ invL l (S O K e)), ϖ.iHat O K (hatR O f') = ϖ.iSD O K ⟨f', hf'⟩ :=
    fun f' hf' => (GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ ⟨f', hf'⟩ (hatR O f') (by
      rw [hatR_of_mem (O := O) (invL_S_le_Rpi l e hf')]
      exact hat_coe_Rpi l e ⟨f', invL_S_le_Rpi l e hf'⟩)).symm
  obtain ⟨n, hn⟩ := hf
  have hC : ((l : S O K e) : K⟦X⟧) ^ n = C ((l : K) ^ n) := by simp
  have hlin : ∀ (i : ℕ) (x : K⟦X⟧), ((l : S O K e) : K⟦X⟧) ^ n * descN K i x =
      descN K i (((l : S O K e) : K⟦X⟧) ^ n * x) := fun i x => by
    rw [hC, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  have hdesc : ∀ i : ℕ, descN K i f ∈ invL l (S O K e) := fun i =>
    ⟨n, by rw [hlin]; exact descN_mem_S e i hn⟩
  set s : S O K e := ⟨_, hn⟩ with hs
  have e0 : (l : OD l O) ^ n * ϖ.iSD O K ⟨f, ⟨n, hn⟩⟩ = crisToOD l O (ϖ.iS O K s) := by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨f, ⟨n, hn⟩⟩ = algebraMap (S O K e) (invL l (S O K e)) s :=
      Subtype.ext (by simp [s])
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K s.2 _
  have ei : ∀ i : ℕ, (l : OD l O) ^ n * ϖ.iSD O K ⟨descN K i f, hdesc i⟩ =
      crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := fun i => by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨descN K i f, hdesc i⟩ =
        algebraMap (S O K e) (invL l (S O K e)) ⟨descN K i s, descN_mem_S e i s.2⟩ :=
      Subtype.ext (by
        change ((l : K⟦X⟧)) ^ n * descN K i f = descN K i (((l : S O K e) : K⟦X⟧) ^ n * f)
        rw [← hlin]
        simp)
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K (descN_mem_S e i s.2) _
  have g0 := congrArg (galOD O g) e0
  rw [map_mul, map_pow, map_natCast] at g0
  have key : (l : OD l O) ^ n * (galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f))) =
      galOD O g (crisToOD l O (ϖ.iS O K s)) -
        ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    rw [hiHat f ⟨n, hn⟩, ← g0, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hiHat _ (hdesc i), ← ei i]
    ring
  have hW := Ideal.mem_span_singleton.2 (taylor_S_mod K ϖ g s R)
  rw [← key] at hW
  exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_l_OD.pow n)).1 hW

theorem galOD_idem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  change galOD O g (toOD l O (constA t _)) = toOD l O (constA t _)
  rw [← crisToOD_toOCr, galOD_crisToOD, galOCr_toOCr, galOA_constA t h]

end Scal2

theorem taylor_iD_mod_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ g hg f hf R
  let g' : ↥(GK (ϖ.field a)) := ⟨g, hg⟩
  have hED : ED K t ϖ = ϖ.iAl O K (EIn l e _) := (glue_const _ _ _).trans (ϖ.iHat_ofAl O K _)
  rw [hED]
  have hfix : ∀ τ, galOD O g (idem (constD t) τ) = idem (constD t) τ := galOD_idem t ϖ g'
  have hsplit : galOD O g (ϖ.iD t K (fun τ => hatR O (f τ))) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) =
      ∑ τ, idem (constD t) τ * (galOD O g (ϖ.iHat O K (hatR O (f τ))) - ∑ i ∈ Finset.range R,
        toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          ϖ.iHat O K (hatR O (descN K i (f τ)))) := by

    simp only [PiSys.iD, glue_apply, map_sum, map_mul, hfix, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (taylor_invL_mod t ϖ g' (hf τ) R)

end GlobalTheory.GalStep
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.dvd_polyEvaluation_of_mem_dividedTwoVariableSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  first | exact @GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet | exact GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet | (intros; apply GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet <;> assumption)
end
