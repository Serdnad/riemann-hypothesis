module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle562
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerLeftCommutesEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle738
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle740
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ExtQis

theorem quasiIso_of_mappingCone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone (Q : ℕ) [NeZero Q] (F : Shv (ZMod Q)) (hF : FlatS F) (n : ℤ) :
    FlatS ((mappingCone (resAug F)).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero (ZMod Q)
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resAug F) n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ ?_)
  · by_cases h : n + 1 = 0
    · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
    · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · have : Injective ((res (ZMod Q) F).X n) :=
      (inferInstance : Injective ((injectiveResolution F).cochainComplex.X n))
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf Q _).2

theorem quasiIso_extAug : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ),
    QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  intro Q q _ hq i
  have hq' : QuasiIso (resAug (tw Q i)) := (inferInstance : QuasiIso (injectiveResolution (tw Q i)).ι')
  have hK : (mappingCone (resAug (tw Q i))).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  have : (res (ZMod Q) (tw Q i)).IsStrictlyGE 0 :=
    (inferInstance : (injectiveResolution (tw Q i)).cochainComplex.IsStrictlyGE 0)
  -- The default `lia` proofs are expensive to check in this context.
  have hneg : (-1 : ℤ) < 0 := neg_one_lt_zero
  have : (mappingCone (resAug (tw Q i))).IsStrictlyGE (-1) :=
    CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1) hneg hneg.le
  have hE := GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q hq (mappingCone (resAug (tw Q i))) (-1)
    (flatS_cone Q (tw Q i) (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q i)) hK
  have hC : (mappingCone (((extSh (ZMod.castHom hq (ZMod q))).mapHomologicalComplex _).map
      (resAug (tw Q i)))).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso (resAug (tw Q i))
      (extSh (ZMod.castHom hq (ZMod q))))
  have h1 := quasiIso_of_mappingCone_acyclic _ hC
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)) := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end GlobalTheory.EtC.ExtQis

end
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

theorem _root_.GlobalTheory.T.fock_action_upper_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  first | exact @GlobalTheory.CharPair.FirstBlock.act_first_block | exact GlobalTheory.CharPair.FirstBlock.act_first_block | (intros; apply GlobalTheory.CharPair.FirstBlock.act_first_block <;> assumption)
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

variable {P Q R : ℕ}

theorem pderiv_detR_wLetter (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename g _ hv)
  simp [g] at hx

theorem wPolarize_aeval_mR (b b' : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c)
        (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p n hp =>
    have key : ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (mR P Q R n.1 n.2)
        = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2)
            (∑ a, X (a, b') * pderiv (a, b) (X n : Mdl P Q)) := by
      obtain ⟨a, b''⟩ := n
      by_cases hb : b'' = b
      · subst hb
        simp [mR, pderiv_X, Pi.single_apply, mul_comm]
      · simp [mR, pderiv_X, Pi.single_apply, hb]
    have e1 : ∀ (A B : Pol P Q R 0), ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (A * B) =
        (∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) A) * B +
          A * ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
        (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    have e2 : ∀ (A B : Mdl P Q), ∑ a, X (a, b') * pderiv (a, b) (A * B) =
        (∑ a, X (a, b') * pderiv (a, b) A) * B + A * ∑ a, X (a, b') * pderiv (a, b) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [map_mul, aeval_X, e1, hp, key, e2, map_add (f := _), map_mul, map_mul, aeval_X]

theorem fockAct1_inr_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  intro P Q R h k b b' G
  have hD : ∀ c : Fin R, pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := fun c => by
    simp [Derivation.leibniz_pow, pderiv_detR_wLetter]
  have hw := wPolarize_aeval_mR (R := R) b b' G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    GlobalTheory.CompactHarm.omE_nn (Sum.inr b, Sum.inl _) (Sum.inr b', Sum.inl _) rfl rfl]
  simp only [embR, opR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, pderiv_mul, hD,
    mul_zero, add_zero, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg, map_smul, Prod.mk.injEq, Sum.inr.injEq, and_true]
  have e : ∀ x : Fin P, (mulM x b') ((derM x b) G) = X (x, b') * pderiv (x, b) G := fun _ => rfl
  simp only [e, ← hw, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, mul_assoc]
  rw [sub_right_inj]
  split_ifs
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring
  · simp

end GlobalTheory.CharPair
end
end

section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

theorem _root_.GlobalTheory.T.fock_action_lower_left_commutes_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  first | exact @GlobalTheory.CharPair.fockAct1_embR_inr_inl | exact GlobalTheory.CharPair.fockAct1_embR_inr_inl | (intros; apply GlobalTheory.CharPair.fockAct1_embR_inr_inl <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe_fin (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N a b (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  simp only [eV, dif_pos (And.intro a.isLt b.isLt)]
  rfl

theorem nablaSchur : NablaSchur := by
  intro N ν hν S hS hfix
  have hc : ∀ (a b : Fin N) (x : dualWeyl ℚ N N ν), eV N ν a b (S x) = S (eV N ν a b x) := by
    intro a b x
    have h := LinearMap.congr_fun (hS a a.isLt b b.isLt) x
    simpa only [Module.End.mul_apply] using h
  set v : dualWeyl ℚ N N ν := ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ with hv

  have hder : ∀ a b : Fin N, a < b →
      Formalism.CohomologicalDescent.LR.der N N a b ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab
    have h1 : eV N ν a b v = 0 := by
      apply Subtype.ext
      rw [eV_coe_fin]
      exact Formalism.CohomologicalDescent.LR.der_hw_raise ν a b hab
    rw [← eV_coe_fin, hc, h1, map_zero]
    rfl
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k →
      rowDiv ℚ a b k ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab k hk
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Formalism.CohomologicalDescent.LR.der_pow a b (ne_of_lt hab), pow_succ, Module.End.mul_apply]
    have h2 := hder a b hab
    change (Formalism.CohomologicalDescent.LR.der N N a b : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) _ = 0 at h2
    rw [h2, map_zero, smul_zero]
  obtain ⟨c, hcv⟩ := hwLine ℚ N N le_rfl ν hν _ (S v).2 hkill
  have hc1 : c = 1 := by
    rw [hcv, Formalism.CohomologicalDescent.LR.fock_smul_right] at hfix
    have hpos := Formalism.CohomologicalDescent.LR.hw_norm_pos ν
    have h3 : (c - 1) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) = 0 := by rw [sub_mul, hfix, one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)
  have hSv : S v = v := by
    apply Subtype.ext
    rw [hcv, hc1, one_smul]

  set M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    (LinearMap.ker (S - 1)).map (dualWeyl ℚ N N ν).subtype with hM
  have hmem : ∀ x : dualWeyl ℚ N N ν, S x = x → (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]
  have hle : M ≤ dualWeyl ℚ N N ν := by
    rintro f ⟨x, _, rfl⟩
    exact x.2
  have hcl : RowDivClosed M := by
    intro a b k
    refine Formalism.CohomologicalDescent.LR.closed_of_der a b M ?_ k
    rintro f ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    have h4 := hmem (eV N ν a b x) (by rw [← hc, hx])
    rw [eV_coe_fin] at h4
    exact h4
  have hhw : hw ℚ le_rfl ν ∈ M := hmem v hSv
  have heq := closedEqNabla N N le_rfl ν hν M hle hcl hhw
  apply LinearMap.ext
  intro x
  have hx : (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy
  rw [Module.End.one_apply]
  exact hy

end GlobalTheory.LeviCut
end
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.adjoint_action_endomorphism_weight_bound : GlobalTheory.LeviCut.AdjBdd := by
  first | exact @GlobalTheory.LeviCut.adjBdd_holds | exact GlobalTheory.LeviCut.adjBdd_holds | (intros; apply GlobalTheory.LeviCut.adjBdd_holds <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.projector_grid_denominator_bound : GlobalTheory.LeviCut.GridInt := by
  first | exact @GlobalTheory.LeviCut.gridInt_holds | exact GlobalTheory.LeviCut.gridInt_holds | (intros; apply GlobalTheory.LeviCut.gridInt_holds <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.projector_value_highest_weight_vector : GlobalTheory.LeviCut.StepScalar := by
  first | exact @GlobalTheory.LeviCut.StepScalarProof.stepScalar | exact GlobalTheory.LeviCut.StepScalarProof.stepScalar | (intros; apply GlobalTheory.LeviCut.StepScalarProof.stepScalar <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.beta_integral_denominator_bound : GlobalTheory.LeviCut.BetaDen := by
  first | exact @GlobalTheory.LeviCut.betaDen | exact GlobalTheory.LeviCut.betaDen | (intros; apply GlobalTheory.LeviCut.betaDen <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeyl_highest_weight_restriction_blockDiagonal : GlobalTheory.LeviCut.ResHw := by
  first | exact @GlobalTheory.LeviCut.resHw_holds | exact GlobalTheory.LeviCut.resHw_holds | (intros; apply GlobalTheory.LeviCut.resHw_holds <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable : GlobalTheory.LeviCut.SubstMem := by
  first | exact @GlobalTheory.LeviCut.substMem | exact GlobalTheory.LeviCut.substMem | (intros; apply GlobalTheory.LeviCut.substMem <;> assumption)
end
