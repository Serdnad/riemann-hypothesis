module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle023
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Mathlib.LinearAlgebra.Lagrange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle042
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle040
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle376
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle755
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle754
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

noncomputable section

namespace GlobalTheory.LatValSum

theorem norm_le_one_of_isIntegral_int {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one {q : ℕ} [Fact q.Prime] {n : ℕ} (hn : n.Coprime q) : ‖(n : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q]) := (map_natCast _ n).symm
  rw [e]
  have h : ‖algebraMap ℚ_[q] ℂ_[q] ((n : ℕ) : ℚ_[q])‖ = ‖((n : ℕ) : ℚ_[q])‖ := PadicComplex.norm_extends' (p := q) _
  rw [h]
  exact Padic.norm_natCast_eq_one_iff.mpr hn.symm

local notation "K" => algebraicClosure ℚ ℂ

theorem valGe_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) →
    (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  intro l hl r J _ u x hu hx
  have : Fact l.Prime := ⟨hl⟩
  have hx' := fun j => (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r (x j ^ 12)).1 (hx j)
  refine (GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding l r _).2 ?_
  intro lam

  have huK : ∀ j, ∃ h : u j ∈ K, ‖lam ⟨u j, h⟩‖ ≤ 1 := by
    intro j
    obtain ⟨n, hn, hint⟩ := hu j
    have hn0 : (n : ℂ) ≠ 0 := by
      have : n ≠ 0 := by
        rintro rfl
        exact hl.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)
      exact_mod_cast this
    have hmK : (n : ℂ) * u j ∈ K :=
      mem_algebraicClosure_iff.mpr (hint.tower_top (A := ℚ)).isAlgebraic
    have hnK : (n : ℂ) ∈ K := IntermediateField.natCast_mem (algebraicClosure ℚ ℂ) n
    have huj : u j = ((n : ℂ) * u j) * (n : ℂ)⁻¹ := by field_simp
    have hK : u j ∈ K := by rw [huj]; exact (algebraicClosure ℚ ℂ).mul_mem hmK ((algebraicClosure ℚ ℂ).inv_mem hnK)
    refine ⟨hK, ?_⟩
    have he : (⟨(n : ℂ) * u j, hmK⟩ : K) = (n : K) * ⟨u j, hK⟩ := Subtype.ext (by simp)
    have hI : IsIntegral ℤ (lam ⟨(n : ℂ) * u j, hmK⟩) := by
      have h2 : IsIntegral ℤ (⟨(n : ℂ) * u j, hmK⟩ : K) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K ℂ) Subtype.val_injective).mp hint
      convert map_isIntegral_int lam h2
      exact Subsingleton.elim _ _
    have h1 := norm_le_one_of_isIntegral_int hI
    rw [he, map_mul, map_natCast, norm_mul, norm_natCast_eq_one hn, one_mul] at h1
    exact h1

  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.pos
  have hpow : ((l : ℝ) ^ (r / 12)) ^ (12 : ℕ) = (l : ℝ) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  have hxK : ∀ j, ∃ h : x j ∈ K, ‖lam ⟨x j, h⟩‖ ≤ (l : ℝ) ^ (r / 12) := by
    intro j
    obtain ⟨h12, hb⟩ := hx' j lam
    have hK : x j ∈ K := mem_algebraicClosure_iff.mpr
      ((mem_algebraicClosure_iff.mp h12).of_pow (by norm_num))
    refine ⟨hK, ?_⟩
    have he : (⟨x j ^ 12, h12⟩ : K) = (⟨x j, hK⟩ : K) ^ 12 := Subtype.ext (by simp)
    rw [he, map_pow, norm_pow, ← hpow] at hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hb
  choose hu1 hu2 using huK
  choose hx1 hx2 using hxK
  have hSK : (∑ j, u j * x j) ∈ K := (algebraicClosure ℚ ℂ).sum_mem fun j _ => (algebraicClosure ℚ ℂ).mul_mem (hu1 j) (hx1 j)
  have hS12 : (∑ j, u j * x j) ^ 12 ∈ K := (algebraicClosure ℚ ℂ).pow_mem hSK 12
  refine ⟨hS12, ?_⟩
  have he : (⟨(∑ j, u j * x j) ^ 12, hS12⟩ : K) = (∑ j, (⟨u j, hu1 j⟩ : K) * ⟨x j, hx1 j⟩) ^ 12 :=
    Subtype.ext (by simp)
  rw [he, map_pow, norm_pow, ← hpow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 12

  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [map_mul, norm_mul]
  calc ‖lam ⟨u j, hu1 j⟩‖ * ‖lam ⟨x j, hx1 j⟩‖ ≤ 1 * (l : ℝ) ^ (r / 12) :=
        mul_le_mul (hu2 j) (hx2 j) (norm_nonneg _) zero_le_one
    _ = (l : ℝ) ^ (r / 12) := one_mul _

end GlobalTheory.LatValSum
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar.TestFn

theorem exists_invariant_test : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ := by
  intro E _ _ _ r X
  have ho : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  have h0 := IW.zero_mem_OmF X (baseFr X) ho
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((OntoB.isOpen_OmF X (baseFr X)).mem_nhds h0)
  set A : Set (V (nd X)) := Metric.closedBall 0 ε with hAdef
  have hA : MeasurableSet A := measurableSet_closedBall
  have hS := GlobalTheory.Unfold.measurableSet_satFrames X ho hA hball
  refine ⟨(GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator 1, measurable_one.indicator hS, ?_, ?_⟩
  · intro x _ b hb
    by_cases hx : x ∈ GlobalTheory.Unfold.satFrames X (baseFr X) A
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mpr hx)]
      rfl
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem fun h => hx ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mp h)]
  have heq : (fun z => (GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (cpt X (baseFr X) z)) = A.indicator 1 := by
    funext z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mpr hz)]
      rfl
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem fun h => hz ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mp h)]
  rw [heq, lintegral_indicator_one hA]
  refine ⟨?_, (GlobalTheory.SatFin.muF_lt_top_of_isCompact X (baseFr X) (isCompact_closedBall _ _) hball).ne⟩
  unfold muF
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (densF X (baseFr X) z))
      (volume.restrict (OmF X (baseFr X))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (OntoB.densF_continuousOn.aemeasurable (OntoB.isOpen_OmF X (baseFr X)).measurableSet)
  rw [Ne, withDensity_apply_eq_zero' hmeas]
  have hset : {z | ENNReal.ofReal (densF X (baseFr X) z) ≠ 0} ∩ A = A := by
    refine Set.inter_eq_right.mpr fun z hz => ?_
    show ENNReal.ofReal (densF X (baseFr X) z) ≠ 0
    exact (ENNReal.ofReal_pos.mpr (OntoB.densF_pos (hball hz))).ne'
  rw [hset, Measure.restrict_apply hA, Set.inter_eq_left.mpr hball]
  exact (Metric.measure_closedBall_pos volume 0 hε).ne'

end GlobalTheory.FlagQuotHaar.TestFn
end

section

open NumberField GlobalTheory.CuspRep

noncomputable section

open Polynomial Finset

namespace GlobalTheory.CuspRep

theorem eval_eq_sum_lagrange_nodes (b : ℕ) (u : ℂ) (f : ℂ[X]) (hf : f.degree < ((b + 1 : ℕ) : WithBot ℕ)) :
    f.eval u = ∑ j : Fin (b + 1),
      (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u * f.eval ((j : ℕ) : ℂ) := by
  have hinj : Set.InjOn (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) (univ : Finset (Fin (b + 1))) := by
    intro x _ y _ h
    exact Fin.ext (by simpa using h)
  have e := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  conv_lhs => rw [e]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm]

theorem cap_eq_sum_nodes (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ) :
    ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ (Sm E b)) b (Eop τ)
  have hcap : ∀ v : ℂ, cap (a := b) τ v =
      ∑ i ∈ range (b + 1), ((X + C (((b : ℂ) - 1) / 2)) ^ i).eval v • c i := by
    intro v
    rw [cap, hc]
    simp only [eval_pow, eval_add, eval_X, eval_C]
  refine ⟨fun j => (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u, ?_⟩
  simp_rw [hcap, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_smul, ← eval_eq_sum_lagrange_nodes]
  have hi' : i < b + 1 := mem_range.1 hi
  rw [degree_pow, degree_X_add_C]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hi'

end GlobalTheory.CuspRep
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]


variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

end GlobalTheory.FinGL.LeviChar
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_coset_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  intro G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, -, -, hfour⟩ := GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ
  obtain ⟨h1, h2⟩ := hfour X Y
  have hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    intro a
    obtain ⟨hmul, -, -, -, hlin⟩ := GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
    have := hmul Y hY _ (hlin (η ^ a))
    convert this using 1
  have hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ) :=
    fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)
  choose m hm using hm
  have hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hl : (Nat.card Γ : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [hm, hN, hcos, hz, mul_zero] at h1 h2
  have hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0 := by
    have h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ))
        = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card Γ) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; push_cast; ring
    rw [h3] at h2
    rw [← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]
    have := h2.symm
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_ne_zero hG hl)
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum
  have hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0 := by
    intro a ha
    exact hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩
  rw [Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ) := by
    push_cast at h1 ⊢
    have h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hl hG)
    · exact sub_eq_zero.1 h
  exact hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩

end GlobalTheory.Shin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.ThetaSys

theorem supI_closedPoint_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    M.HasDiv S.th → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z)
    (emb : Ω →+* FractionRing V), (∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U →
      emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f)) →
    S.supI M (ξ (IsLocalRing.closedPoint V)) =
      {a | S.th a ≠ 0 ∧ ∀ b, ∃ v : V, emb (S.th b) = algebraMap V (FractionRing V) v * emb (S.th a)} := by
  intro o Ω _ _ _ S M hD V _ _ _ ξ emb hemb
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  have hs : ξ (IsLocalRing.closedPoint V) ⤳ z := specializes_rfl
  have key : ∀ (x : Ω) (hx : x ∈ M.O z), emb x = algebraMap V (FractionRing V) (RatModel.valLoc ξ z hs ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨U, f, hz, rfl⟩ := hx
    rw [RatModel.valLoc_valF ξ hs hz f]
    exact hemb U f hz
  ext a
  simp only [supI, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, fun b => ⟨RatModel.valLoc ξ z hs ⟨_, hb b⟩, ?_⟩⟩
    rw [← key _ (hb b), ← map_mul, div_mul_cancel₀ _ ha]
  · rintro ⟨ha, hc⟩
    obtain ⟨x₀, hx₀⟩ := hD z
    obtain ⟨v, hv⟩ := hc x₀
    have hea : emb (S.th a) ≠ 0 := (map_ne_zero emb).2 ha
    have hw := key _ (hx₀.2 a)
    have hunit : IsUnit (RatModel.valLoc ξ z hs ⟨_, hx₀.2 a⟩) := by
      refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
      have hv0 : algebraMap V (FractionRing V) v ≠ 0 := by
        intro h0
        exact (map_ne_zero emb).2 hx₀.1 (by rw [hv, h0, zero_mul])
      rw [map_mul, map_one, ← hw, map_div₀, hv]
      field_simp
    have hu : IsUnit (⟨S.th a / S.th x₀, hx₀.2 a⟩ : M.O z) :=
      (RatModel.isUnit_valLoc_iff ξ hzdef.symm _).1 hunit
    exact (hx₀.div_iff_isUnit a).2 hu

end GlobalTheory.ZH.ThetaSys
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem RatModel.IsCl.subfield_eq_top_of_ratios {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {M : RatModel o Ω} {J : Type} {t : J → Ω} (h : M.IsCl t) (K : Subfield Ω)
    (hc : ∀ a, algebraMap o Ω a ∈ K) (hr : ∀ i j, t j / t i ∈ K) : K = ⊤ := by
  obtain ⟨i, hi⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, by rw [hD]; exact hi⟩
  let A : Subalgebra o Ω := { K.toSubring with algebraMap_mem' := hc }
  have hle : M.ringOn U ≤ A := by
    rw [hR]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact hr i j
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_closure_theta_ratios_of_isCl (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) (J : Type) (t : J → Ω) (h : M.IsCl t) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  obtain ⟨x, hx⟩ := S.th_ne
  have htop := h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)}))
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ hx).symm⟩))
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]
  exact Subfield.mem_top y

end GlobalTheory.ZH
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_lift_of_isProper_of_isHom_id' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  first | exact @GlobalTheory.exists_lift_of_isProper_of_isHom_id | exact GlobalTheory.exists_lift_of_isProper_of_isHom_id | (intros; apply GlobalTheory.exists_lift_of_isProper_of_isHom_id <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.PinchUniq.uniq | exact GlobalTheory.PinchUniq.uniq | (intros; apply GlobalTheory.PinchUniq.uniq <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial

theorem _root_.GlobalTheory.T.lineDegree_eq_sum_of_scalar_split : ∀ (k E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field E] [Algebra k E], IsFF k E → ∀ (m n : ℕ) (G : Place k E → Matrix (Fin 2) (Fin 2) E), admitted G → ∀ (S : Place k E → Matrix (Fin n) (Fin n) E) (q : Fin n → E) (c : E) (w : Fin m → Fin 2 → E), c ≠ 0 → (∀ j, w j ≠ 0) → (∀ P, ordVec P ((S P).mulVec q) = ord P c + ∑ j, ordVec P ((G P).mulVec (w j))) → degLine S q = ∑ j, degLine G (w j) := by
  first | exact @GlobalTheory.Nef.degLine_eq_sum_of_split | exact GlobalTheory.Nef.degLine_eq_sum_of_split | (intros; apply GlobalTheory.Nef.degLine_eq_sum_of_split <;> assumption)
end
