module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle623
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle624
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntertwinerUnipotentInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle338
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle640
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle622
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
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle199
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle626

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_hodge_basis_deRham_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  first | (exact @GlobalTheory.HodgeEx.exists_hodge) | (exact GlobalTheory.HodgeEx.exists_hodge) | (intros; apply GlobalTheory.HodgeEx.exists_hodge  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C, ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  first | exact @GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | exact GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | (intros; apply GlobalTheory.BSP.C_mem_δLocus_of_hausdorff <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_deltaRingStructure_adicCompletion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  first | exact @GlobalTheory.BSP.exists_delta_completion | exact GlobalTheory.BSP.exists_delta_completion | (intros; apply GlobalTheory.BSP.exists_delta_completion <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.prismaticEnvelopeRelation_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  first | exact @GlobalTheory.EnvShape.envRel_triangular | exact GlobalTheory.EnvShape.envRel_triangular | (intros; apply GlobalTheory.EnvShape.envRel_triangular <;> assumption)
end

section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

noncomputable section

namespace GlobalTheory.SerSys.ParVec

open GlobalTheory.GLq.Opp GlobalTheory.SerSys.Opp MonoidAlgebra

private theorem inPar_tl_br_par_one {g : ℕ} [Fact g.Prime] {a b : ℕ} (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    InPar a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) ∧
    tl a ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 ∧
    br a b ((par finSumFinEquiv (1 : Gn g a) B 1 : Gn g (a + b)) : Mt g (a + b)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i' with i' | i'
    · have := i'.isLt
      simp at hi
      omega
    · rcases j' with j' | j'
      · simp
      · simp at hj
  · ext i j
    show entN _ i j = _
    rw [(entN_par (1 : Gn g a) B 1 i j).1 i.isLt j.isLt]
    simp [entN]
  · ext i j
    show entN _ (a + i) (a + j) = _
    rw [(entN_par (1 : Gn g a) B 1 i j).2.2.1]
    simp [entN]

theorem has_mul_of_isParVec : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  intro g _ S n V _ _ π a b χ h f v hn hχ hv hne
  subst hn
  obtain ⟨hvK, hrad, hy⟩ := hv
  let v' : fixK1 π := ⟨v, hvK⟩
  have hA : ∀ x : Gn g a, blk a b (a + b) x 1 = inA finSumFinEquiv x := fun x => blk_eq x 1
  have hB : ∀ y : Gn g b, blk a b (a + b) 1 y = inB finSumFinEquiv y := fun y => blk_eq 1 y
  let ρA : Representation ℂ (Gn g a) (fixK1 π) := (repK π).comp (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let ρB : Representation ℂ (Gn g b) (fixK1 π) := (repK π).comp (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)))
  let u : fixK1 π := ρA.asAlgebraHom (S.e a f) v'
  have hu : (u : V) = actTop π a b (S.e a f) v := by
    show ((ρA.asAlgebraHom (S.e a f) v' : fixK1 π) : V) = _
    rw [alg_apply, actTop, Submodule.coe_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hA]
    rfl
  have hv1 : ρB.asAlgebraHom (S.e b h) v' = v' := by
    rw [alg_apply]
    have hyv : ∀ y : Gn g b, ρB y v' = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • v' := by
      intro y
      apply Subtype.ext
      show π (lift g (a + b) (inB finSumFinEquiv y)) v = _
      rw [← hB]
      exact hy y
    simp_rw [hyv, smul_smul, ← Finset.sum_smul]
    have hev := (Loc.charIn_iff S χ b h).1 hχ
    simp only [Loc.ev] at hev
    rw [hev, one_smul]
  have key : (repK π).asAlgebraHom (S.e (a + b) (f * h)) u = u := by
    apply S.mul a b (a + b) rfl f h (fixK1 π) (repK π) u
    · intro u0 h0 h1 h2
      obtain ⟨B, rfl⟩ := eq_par (k := a) (l := b) u0 h0 h1 h2
      show (repK π) _ (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'

      rw [alg_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul]
      congr 1
      have hconj : par finSumFinEquiv 1 B 1 * inA finSumFinEquiv x =
          inA finSumFinEquiv x * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1 := by
        show par finSumFinEquiv 1 B 1 * par finSumFinEquiv x 0 1 =
          par finSumFinEquiv x 0 1 * par finSumFinEquiv 1 (((x⁻¹ : Gn g a) : Mt g a) * B) 1
        rw [par_mul, par_mul]
        simp [← Matrix.mul_assoc]
      show (repK π) (par finSumFinEquiv 1 B 1) ((repK π) (inA finSumFinEquiv x) v') = (repK π) (inA finSumFinEquiv x) v'
      rw [← Module.End.mul_apply, ← map_mul, hconj, map_mul, Module.End.mul_apply]
      congr 1
      obtain ⟨r0, r1, r2⟩ := inPar_tl_br_par_one (g := g) (((x⁻¹ : Gn g a) : Mt g a) * B)
      exact Subtype.ext (hrad _ r0 r1 r2)
    · simp_rw [hA]
      have e2 : ∑ x, (S.e a f).coeff x • (repK π) (inA finSumFinEquiv x) u = ρA.asAlgebraHom (S.e a f) u := by
        rw [alg_apply]
        rfl
      rw [e2]
      show ρA.asAlgebraHom (S.e a f) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      rw [← Module.End.mul_apply, ← map_mul, S.idem]
    · simp_rw [hB]
      have e3 : ∑ y, (S.e b h).coeff y • (repK π) (inB finSumFinEquiv y) u = ρB.asAlgebraHom (S.e b h) u := by
        rw [alg_apply]
        rfl
      rw [e3]
      show ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') = ρA.asAlgebraHom (S.e a f) v'
      have hc : ρB.asAlgebraHom (S.e b h) (ρA.asAlgebraHom (S.e a f) v') =
          ρA.asAlgebraHom (S.e a f) (ρB.asAlgebraHom (S.e b h) v') := by
        simp only [ρA, ρB, comp_alg]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          (commute_AB finSumFinEquiv (S.e a f) (S.e b h)).eq]
      rw [hc, hv1]
  refine ⟨(u : V), u.2, ?_⟩
  rw [← repK_alg, key, hu]
  exact hne

end GlobalTheory.SerSys.ParVec
end
end

section

noncomputable section

namespace GlobalTheory.SerSys.OfLabel

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blk_eq_par {a b : ℕ} (x : Gn g a) (y : Gn g b) : blk a b (a + b) x y = par finSumFinEquiv x 0 y := by
  refine Supp.ext_entN fun i j hi hj => ?_
  rw [ParInd.blk_val, entN, dite_eq_left ⟨hi, hj⟩, ParInd.dg]
  dsimp only
  by_cases h1 : i < a <;> by_cases h2 : j < a
  · rw [(Supp.entN_par _ _ _ i j).1 h1 h2, if_pos ⟨h1, h2⟩]
  · rw [(Supp.entN_par _ _ _ i j).2.2.2 rfl h1 (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [(Supp.entN_par _ _ _ i j).2.1 (by omega) h2, if_neg (by omega), if_neg (by omega)]
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h1)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h2)
    rw [(Supp.entN_par _ _ _ i j).2.2.1, if_neg (by omega), if_pos (by omega)]
    simp

def ofLabel (L : LabelDatum g) (h5 : 5 ≤ g) (hG : Green) : Sys g where
  e := eSerC L
  idem n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).1
  central n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.1
  orth n := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.1
  label n f h := by by_contra h'; exact h ((GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.1 f h')
  sum n := by obtain ⟨S, -, h⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG n).2.2.2.2; exact ⟨S, h⟩
  mul a b n hn f f' V _ _ ρ v h0 h1 h2 := by
    subst hn
    have hN : ρ.asAlgebraHom (eN g (finSumFinEquiv (m := a) (n := b))) v = v := eN_right _ ρ v fun B => by
      refine h0 _ (fun i j hj hi => ?_) ?_ ?_
      · rw [← ParInd.entN_self (par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b)).val]
        exact (Supp.entN_par _ _ _ i j).2.1 hi hj
      · ext i j
        rw [tl, (Supp.entN_par _ _ _ i j).1 i.2 j.2, ParInd.entN_self]; rfl
      · ext i j
        rw [br, (Supp.entN_par _ _ _ i j).2.2.1, ParInd.entN_self]; rfl
    have hA : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (eSerC L a f)) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h1; exact h1
    have hB : ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (eSerC L b f')) v = v := by
      rw [← comp_alg, Supp.alg_apply]; simp only [blk_eq_par] at h2; exact h2
    obtain ⟨S, -, hS⟩ := (GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L h5 hG (a + b)).2.2.2.2
    have hz : ∀ F, F ≠ f * f' → ρ.asAlgebraHom (eSerC L (a + b) F) v = 0 := fun F hF => by
      have hv := ser_vanish' L h5 hG (finSumFinEquiv (m := a) (n := b)) F f f' hF
      have := congrArg (fun z => ρ.asAlgebraHom z v) hv
      simpa only [map_mul, Module.End.mul_apply, hN, hA, hB, map_zero, LinearMap.zero_apply] using this
    have e : v = ∑ F ∈ S, ρ.asAlgebraHom (eSerC L (a + b) F) v := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← LinearMap.sum_apply, ← map_sum, hS, map_one, Module.End.one_apply]
    by_cases hm : f * f' ∈ S
    · rw [Finset.sum_eq_single_of_mem _ hm fun F _ hF => hz F hF] at e; exact e.symm
    · rw [Finset.sum_eq_zero fun F hF => hz F (by rintro rfl; exact hm hF)] at e; rw [e]; simp

end GlobalTheory.SerSys.OfLabel
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  exact @GlobalTheory.HorizPole.main
end

section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem injective_of_charZero {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {K : Type} [Field K] [CharZero K]
    (f : Wq l a →+* K) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l a) w h0
  rw [map_mul, map_pow, map_natCast] at hw
  have hb : f b ≠ 0 := (b.isUnit.map f).ne_zero
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact mul_ne_zero (pow_ne_zero m hl) hb hw

theorem emb_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact injective_of_charZero ((algebraMap O K).comp (emb t τ).toRingHom)

end GlobalTheory.CrysPrism
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_ofA_of_injective [NeZero a] (hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)))
    (P : PhiMod O K l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (hβ : ∀ τ j i, E K l e ^ β * P.mxInv τ j i ∈ A O K) (τ : ZMod a) (j i : ι) :
    y τ j i = ofA O K l e ⟨E K l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  apply hinj
  rw [hy, ← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) _
    (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

end Gen

end GlobalTheory.BK.CoordInv


open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv_eq_ofA : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P β y hy hβ τ j i
  exact eq_ofA_of_injective (algebraMap_AhatE_injective l e) P β y hy hβ τ j i
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l, (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  first | exact @GlobalTheory.TameCoeff.main | exact GlobalTheory.TameCoeff.main | (intros; apply GlobalTheory.TameCoeff.main <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  first | exact @GlobalTheory.BK.coordE_mxInv | exact GlobalTheory.BK.coordE_mxInv | (intros; apply GlobalTheory.BK.coordE_mxInv <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  first | exact @GlobalTheory.CrysExt.exists_coord | exact GlobalTheory.CrysExt.exists_coord | (intros; apply GlobalTheory.CrysExt.exists_coord <;> assumption)
end
