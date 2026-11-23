module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle016
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle002
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceDecomp

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n),
    ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ g = x * y := by
  intro L _ _ _ n v κ
  classical
  set e : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] GlobalTheory.InertUmax.sgl L v 1 with he_def
  have hsgl : GlobalTheory.InertUmax.sgl L v 1 * GlobalTheory.InertUmax.sgl L v 1 = GlobalTheory.InertUmax.sgl L v 1 := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    change GlobalTheory.InertUmax.sgl L v 1 w * GlobalTheory.InertUmax.sgl L v 1 w = GlobalTheory.InertUmax.sgl L v 1 w
    rcases eq_or_ne w v with rfl | hw
    · simp only [GlobalTheory.InertUmax.sgl_same, mul_one]
    · simp only [GlobalTheory.InertUmax.sgl_ne L _ _ hw, mul_zero]
  have he2 : e * e = e := by rw [he_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hsgl]
  have hce : conjAL L e = e := by simp [he_def, conjAL, Algebra.TensorProduct.map_tmul]
  have hcv : compAt L v e = 1 := by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_same]; rfl
  have hcw : ∀ w, w ≠ v → compAt L w e = 0 := fun w hw => by
    rw [he_def, GlobalTheory.InertUmax.compAt_tmul, GlobalTheory.InertUmax.sgl_ne L _ _ hw, TensorProduct.tmul_zero]
  let θ : AL L × AL L →+* AL L :=
    { toFun := fun q => e * q.1 + (1 - e) * q.2
      map_one' := by simp only [Prod.fst_one, Prod.snd_one]; ring
      map_mul' := fun q q' => by
        simp only [Prod.fst_mul, Prod.snd_mul]
        linear_combination (-(q.1 * q'.1 - q.1 * q'.2 - q.2 * q'.1 + q.2 * q'.2)) * he2
      map_zero' := by simp
      map_add' := fun q q' => by simp only [Prod.fst_add, Prod.snd_add]; ring }
  have hθ : ∀ q, θ q = e * q.1 + (1 - e) * q.2 := fun _ => rfl
  have hθc : ∀ a b, conjAL L (θ (a, b)) = θ (conjAL L a, conjAL L b) := by
    intro a b; rw [hθ, hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hce]
  have hθv : ∀ q, compAt L v (θ q) = compAt L v q.1 := by
    intro q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcv]; ring
  have hθw : ∀ w, w ≠ v → ∀ q, compAt L w (θ q) = compAt L w q.2 := by
    intro w hw q; rw [hθ, map_add (f := _), map_mul, map_mul, map_sub, map_one, hcw w hw]; ring
  let pr : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L × AL L) :=
    fun A B i j => (A i j, B i j)
  have pr_mul : ∀ A B C D, pr A B * pr C D = pr (A * C) (B * D) := by
    intro A B C D; ext i j
    · show (∑ l, pr A B i l * pr C D l j).1 = ∑ l, A i l * C l j
      rw [Prod.fst_sum]; rfl
    · show (∑ l, pr A B i l * pr C D l j).2 = ∑ l, B i l * D l j
      rw [Prod.snd_sum]; rfl
  have pr_one : pr 1 1 = 1 := by
    ext i j <;> by_cases h : i = j <;> simp [pr, Matrix.one_apply, h]
  let M : Matrix (Fin n) (Fin n) (AL L) → Matrix (Fin n) (Fin n) (AL L) →
      Matrix (Fin n) (Fin n) (AL L) :=
    fun A B => (pr A B).map θ
  have hM : ∀ A B i j, M A B i j = e * A i j + (1 - e) * B i j := fun _ _ _ _ => rfl
  have M_mul : ∀ A B C D, M A B * M C D = M (A * C) (B * D) := by
    intro A B C D; show (pr A B).map θ * (pr C D).map θ = (pr (A * C) (B * D)).map θ
    rw [← Matrix.map_mul, pr_mul]
  have M_one : M 1 1 = 1 := by
    show (pr 1 1).map θ = 1
    rw [pr_one, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have M_conj : ∀ A B, conjT (conjAL L) (M A B) = M (conjT (conjAL L) A) (conjT (conjAL L) B) := by
    intro A B; ext i j
    show conjAL L (θ (A j i, B j i)) = θ (conjAL L (A j i), conjAL L (B j i))
    exact hθc _ _
  have M_diag : ∀ A, M A A = A := by intro A; ext i j; rw [hM]; ring
  set K : Matrix (Fin n) (Fin n) (AL L) := ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    with hK
  have hKK : K * conjT (conjAL L) K = 1 := κ.2
  have hX : M K 1 * conjT (conjAL L) (M K 1) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  have hY : M 1 K * conjT (conjAL L) (M 1 K) = 1 := by
    rw [M_conj, M_mul, hKK, conjT_one, Matrix.mul_one, M_one]
  let gX : GL (Fin n) (AL L) := ⟨M K 1, conjT (conjAL L) (M K 1), hX, mul_eq_one_comm.mp hX⟩
  let gY : GL (Fin n) (AL L) := ⟨M 1 K, conjT (conjAL L) (M 1 K), hY, mul_eq_one_comm.mp hY⟩
  have hc1 : ∀ w i j, compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro w i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨gX, hX⟩, ⟨gY, hY⟩, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := hw
    ext i j
    show compAt L w (θ (K i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = _
    rw [hθw w hw', hc1]
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    show compAt L w (θ ((1 : Matrix (Fin n) (Fin n) (AL L)) i j, K i j)) = _
    rw [hθv, hc1]
  · apply Subtype.ext; apply Units.ext
    show K = M K 1 * M 1 K
    rw [M_mul, Matrix.mul_one, Matrix.one_mul, M_diag]

end GlobalTheory.PlaceDecomp
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd


open GlobalTheory.SplitCongNbhd in
theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeAverage


open Classical in
theorem finsum_translate_eq {G : Type} [Group G] (J J' : Subgroup G) (h : G)
    (hconj : ∀ κ ∈ J', h⁻¹ * κ * h ∈ J)
    (hfin : {c : G ⧸ J' | ∃ x ∈ (J : Set G), (x : G ⧸ J') = c}.Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] (f : G → W), (∀ κ ∈ J, ∀ g, f (g * κ) = f g) → ∀ g : G,
      (∑ᶠ c : G ⧸ J', if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
      m • ∑ᶠ d : G ⧸ J, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0 := by
  let φ : G ⧸ J' → G ⧸ J := fun c => ((c.out * h : G) : G ⧸ J)
  have hφ : ∀ x : G, φ (x : G ⧸ J') = ((x * h : G) : G ⧸ J) := by
    intro x
    have h1 : ((x : G ⧸ J').out)⁻¹ * x ∈ J' := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine QuotientGroup.eq.2 ?_
    have := hconj _ h1
    convert this using 1
    group
  have hφs : ∀ (u : G) (c : G ⧸ J'), φ (u • c) = u • φ c := by
    intro u c
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_mk, hφ, hφ, MulAction.Quotient.smul_mk]
      simp [mul_assoc]
  let S : Finset (G ⧸ J') := hfin.toFinset
  have hS : ∀ c, c ∈ S ↔ ∃ x ∈ (J : Set G), (x : G ⧸ J') = c := fun c => hfin.mem_toFinset
  have hSs : ∀ u ∈ J, ∀ c ∈ S, u • c ∈ S := by
    intro u hu c hc
    obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
    exact (hS _).2 ⟨u * x, J.mul_mem hu hx, rfl⟩
  have hT : ∀ d, d ∈ S.image φ ↔ ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d := by
    intro d
    rw [Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
      exact ⟨x * h, ⟨x, hx, 1, J.one_mem, by simp⟩, (hφ x).symm⟩
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : G ⧸ J'), (hS _).2 ⟨u, hu, rfl⟩, ?_⟩
      rw [hφ]
      exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hu')
  have hcard : ∀ d ∈ S.image φ, (S.filter (fun c => φ c = d)).card =
      (S.filter (fun c => φ c = (h : G ⧸ J))).card := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨u, hu, rfl⟩ := (hS c).1 hc
    have e : φ (u : G ⧸ J') = u • (h : G ⧸ J) := by rw [hφ]; rfl
    symm
    refine Finset.card_nbij' (fun c => u • c) (fun c => u⁻¹ • c) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u hu c hc.1, by rw [hφs, hc.2, e]⟩
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u⁻¹ (J.inv_mem hu) c hc.1, by rw [hφs, hc.2, e, inv_smul_smul]⟩
    · intro c _
      simp
    · intro c _
      simp
  refine ⟨(S.filter (fun c => φ c = (h : G ⧸ J))).card, ?_, ?_⟩
  · refine Finset.card_pos.2 ⟨((1 : G) : G ⧸ J'), Finset.mem_filter.2 ⟨(hS _).2 ⟨1, J.one_mem, rfl⟩, ?_⟩⟩
    rw [hφ, one_mul]
  intro W _ f hf g
  let F : G ⧸ J → W := fun d => f (g * d.out)
  have hF : ∀ y : G, F (y : G ⧸ J) = f (g * y) := by
    intro y
    have h1 : ((y : G ⧸ J).out)⁻¹ * y ∈ J := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have := hf _ h1 (g * (y : G ⧸ J).out)
    show f (g * (y : G ⧸ J).out) = _
    rw [← this]
    congr 1
    group
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := S.image φ)]
  · have e1 : (∑ c ∈ S, if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
        ∑ c ∈ S, F (φ c) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' := (hS c).1 hc
      rw [dite_eq_left hc']
      conv_rhs => rw [← hc'.choose_spec.2, hφ, hF]
      rw [mul_assoc]
    have e2 : (∑ d ∈ S.image φ, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0) = ∑ d ∈ S.image φ, F d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := (hT d).1 hd
      rw [dite_eq_left hd']
      conv_rhs => rw [← hd'.choose_spec.2, hF]
    rw [e1, e2, Finset.sum_comp F φ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← hcard d hd]
  · intro d hd
    by_contra hn
    exact hd (dif_neg fun h' => hn (Finset.mem_coe.2 ((hT d).2 h')))
  · intro c hc
    by_contra hn
    exact hc (dif_neg fun h' => hn (Finset.mem_coe.2 ((hS c).2 h')))

theorem heckeD_rt_eq_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (h : GAf L n), J' ≤ J → (∀ κ ∈ J', h⁻¹ * κ * h ∈ J) → {c : GAf L n ⧸ J' | ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ J') = c}.Finite → ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ J, NG.rt L n κ f = f) → NG.heckeD J' (J : Set (GAf L n)) (NG.rt L n h f) = (m : ℂ) • NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'} f := by
  intro L _ _ _ n J J' h _ hconj hfin
  obtain ⟨m, hm, H⟩ := finsum_translate_eq J J' h hconj hfin
  refine ⟨m, hm, fun W _ _ f hf => ?_⟩
  funext g
  have := H W f (fun κ hκ g => congrFun (hf κ hκ) g) g
  rw [Pi.smul_apply, Nat.cast_smul_eq_nsmul]
  exact this

end GlobalTheory.HeckeAverage
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockConj

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem rt_rt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (a b : GAf L n) (f : GAf L n → W) (g : GAf L n) : NG.rt L n a (NG.rt L n b f) g = f (g * a * b) := rfl

end GlobalTheory.TypeBlockConj

namespace GlobalTheory.TypeBlockConj


end GlobalTheory.TypeBlockConj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isoRep_of_stable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n A B _ _ _ _ ρa ρb S₁ S₂ W h₁ h₂ hW hst h0 h0' hne
  have inj1 : ∀ w ∈ W, w.1 = 0 → w = 0 := by
    intro w hw e
    have : w = (0, w.2) := Prod.ext e rfl
    have h2 := h0 w.2 (this ▸ hw)
    exact Prod.ext e h2
  have inj2 : ∀ w ∈ W, w.2 = 0 → w = 0 := by
    intro w hw e
    have : w = (w.1, 0) := Prod.ext rfl e
    have h2 := h0' w.1 (this ▸ hw)
    exact Prod.ext h2 e
  obtain ⟨w₀, hw₀, hw₀ne⟩ := (Submodule.ne_bot_iff W).1 hne
  have le1 : W.map (LinearMap.fst ℂ _ _) ≤ S₁ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).1
  have le2 : W.map (LinearMap.snd ℂ _ _) ≤ S₂ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).2
  have e1 : W.map (LinearMap.fst ℂ _ _) = S₁ := by
    refine (h₁.2.2 _ ⟨le1.trans h₁.1.1, ?_⟩ le1).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.1 ∈ W.map (LinearMap.fst ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj1 w₀ hw₀ this)
  have e2 : W.map (LinearMap.snd ℂ _ _) = S₂ := by
    refine (h₂.2.2 _ ⟨le2.trans h₂.1.1, ?_⟩ le2).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.2 ∈ W.map (LinearMap.snd ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj2 w₀ hw₀ this)
  let p₁ : W →ₗ[ℂ] S₁ := ((LinearMap.fst ℂ _ _).comp W.subtype).codRestrict S₁ (fun w => (hW w.1 w.2).1)
  let p₂ : W →ₗ[ℂ] S₂ := ((LinearMap.snd ℂ _ _).comp W.subtype).codRestrict S₂ (fun w => (hW w.1 w.2).2)
  have b₁ : Function.Bijective p₁ := by
    refine ⟨(injective_iff_map_eq_zero p₁).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj1 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.fst ℂ _ _) := by rw [e1]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  have b₂ : Function.Bijective p₂ := by
    refine ⟨(injective_iff_map_eq_zero p₂).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj2 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.snd ℂ _ _) := by rw [e2]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  refine ⟨(LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂), ?_⟩
  intro h f f' hf
  obtain ⟨w, rfl⟩ := b₁.2 f
  have hf' : f' = p₁ ⟨_, hst h w.1 w.2⟩ := Subtype.ext hf
  subst hf'
  have key : ∀ v : W, ((LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂)) (p₁ v) = p₂ v := by
    intro v
    have : (LinearEquiv.ofBijective p₁ b₁).symm (p₁ v) = v :=
      (LinearEquiv.ofBijective p₁ b₁).symm_apply_apply v
    rw [LinearEquiv.trans_apply, this]; rfl
  rw [key, key]
  rfl

end GlobalTheory
end
