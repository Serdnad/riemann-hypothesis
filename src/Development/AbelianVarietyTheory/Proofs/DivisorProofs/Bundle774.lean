module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionLatticeTensorOfSubstitutionSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorGridScalarOfProjectorScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvariance
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle741
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle726
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle733
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021

@[expose] public section

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.dualWeylRestrictionLatticeTensor_of_substitutionStable : GlobalTheory.LeviCut.SubstMem → GlobalTheory.LeviCut.ResLat := by
  first | exact @GlobalTheory.LeviCut.resLat_of_substMem | exact GlobalTheory.LeviCut.resLat_of_substMem | (intros; apply GlobalTheory.LeviCut.resLat_of_substMem <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.grid_invariance_of_rank_one_two : GlobalTheory.LeviCut.RankOne → GlobalTheory.LeviCut.RankTwo → GlobalTheory.LeviCut.GridInv := by
  first | exact @GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | exact GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | (intros; apply GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.projectorGridScalar_of_projectorScalar : GlobalTheory.LeviCut.StepScalar → GlobalTheory.LeviCut.GridScalar := by
  first | exact @GlobalTheory.LeviCut.gridScalar_of_stepScalar | exact GlobalTheory.LeviCut.gridScalar_of_stepScalar | (intros; apply GlobalTheory.LeviCut.gridScalar_of_stepScalar <;> assumption)
end

section

open GlobalTheory.LeviCut

theorem _root_.GlobalTheory.T.rank_two_consecutive_projector_invariance : GlobalTheory.LeviCut.RankTwo := by
  first | exact @GlobalTheory.LeviCut.RankTwoProof.rankTwo | exact GlobalTheory.LeviCut.RankTwoProof.rankTwo | (intros; apply GlobalTheory.LeviCut.RankTwoProof.rankTwo <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem rTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ A A) (x y : A ⊗[ℚ] B) :
    LinearMap.rTensor B (D : A →ₗ[ℚ] A) (x * y) =
      x * LinearMap.rTensor B (D : A →ₗ[ℚ] A) y + y * LinearMap.rTensor B (D : A →ₗ[ℚ] A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, add_tmul]
      rw [mul_comm b' b]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem lTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (x y : A ⊗[ℚ] B) :
    LinearMap.lTensor A (D : B →ₗ[ℚ] B) (x * y) =
      x * LinearMap.lTensor A (D : B →ₗ[ℚ] B) y + y * LinearMap.lTensor A (D : B →ₗ[ℚ] B) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, tmul_add]
      rw [mul_comm a' a]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem natAdd_ne_castAdd' {p q : ℕ} (b : Fin q) (d : Fin p) : Fin.natAdd p b ≠ Fin.castAdd q d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem castAdd_ne_natAdd' {p q : ℕ} (a : Fin p) (d : Fin q) : Fin.castAdd q a ≠ Fin.natAdd p d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem resT_der_left_X (p q : ℕ) (c d : Fin p) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) (X v)) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]
    | right t =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
  | right b =>
    rw [if_neg (natAdd_ne_castAdd' b d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]

theorem resT_der_right_X (p q : ℕ) (c d : Fin q) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) (X v)) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    rw [if_neg (castAdd_ne_natAdd' a d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]
  | right b =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
    | right t =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]

theorem weight_rowW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (x : Fin N) :
    Finsupp.weight (rowW N N) m x = ∑ s, m (x, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [rowW, Pi.single_apply]

theorem weight_colW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (y : Fin N) :
    Finsupp.weight (colW N N) m y = ∑ a, m (a, y) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

theorem resT_monomial_eq_zero (p q : ℕ) (m : Fin (p + q) × Fin (p + q) →₀ ℕ) (a : ℚ)
    (v : Fin (p + q) × Fin (p + q)) (hv : resVarT ℚ p q v = 0) (hm : m v ≠ 0) : resT ℚ p q (monomial m a) = 0 := by
  rw [resT, aeval_monomial]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm) (by simp only [hv]; exact zero_pow hm)

theorem resVarT_castAdd_natAdd (p q : ℕ) (a : Fin p) (t : Fin q) :
    resVarT ℚ p q (Fin.castAdd q a, Fin.natAdd p t) = 0 := by simp [resVarT]

theorem resVarT_natAdd_castAdd (p q : ℕ) (b : Fin q) (s : Fin p) :
    resVarT ℚ p q (Fin.natAdd p b, Fin.castAdd q s) = 0 := by simp [resVarT]

theorem resT_wrong_degree (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (ν : Fin (p + q) → ℕ) (t : ℚ)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f ν)
    (hsum : ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f)
    (ht : t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ)) : resT ℚ p q f = 0 := by

  rw [f.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff f m ≠ 0 := mem_support_iff.1 hm
  by_contra hne
  have h1 : ∀ (a : Fin p) (t' : Fin q), m (Fin.castAdd q a, Fin.natAdd p t') = 0 := by
    intro a t'
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_castAdd_natAdd p q a t') h0)
  have h2 : ∀ (b : Fin q) (s : Fin p), m (Fin.natAdd p b, Fin.castAdd q s) = 0 := by
    intro b s
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_natAdd_castAdd p q b s) h0)
  have hw : Finsupp.weight (colW (p + q) (p + q)) m = ν := hf hc
  have ht' : t = ∑ c : Fin p, ((Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) : ℕ) : ℚ) := by
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    rw [coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at h3
    simp only [Formalism.CohomologicalDescent.LR.coeff_der_diag] at h3
    rw [← Finset.sum_mul] at h3
    exact (mul_right_cancel₀ hc h3).symm
  have key : ∑ c : Fin p, Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) =
      ∑ c : Fin p, Finsupp.weight (colW (p + q) (p + q)) m (Fin.castAdd q c) := by
    simp only [weight_rowW_apply, weight_colW_apply, Fin.sum_univ_add, h1, h2, Finset.sum_const_zero, add_zero]
    exact Finset.sum_comm
  apply ht
  rw [ht', ← hw]
  exact_mod_cast key

theorem dualWeyl_resDer : ResDer := by
  intro p q f
  refine ⟨fun c d => ?_, fun c d => ?_, fun ν t hf hsum ht => resT_wrong_degree p q f ν t hf hsum ht⟩
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, rTensor_der_mul, resT_der_left_X, hg]
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, lTensor_der_mul, resT_der_right_X, hg]

end GlobalTheory.LeviCut
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  first | exact @GlobalTheory.ScalarPoin.qS_rmul | exact GlobalTheory.ScalarPoin.qS_rmul | (intros; apply GlobalTheory.ScalarPoin.qS_rmul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

theorem _root_.GlobalTheory.T.exists_affine_etale_pullback_coordinates_goodCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (D δ : ℕ) (U : X.Opens), GlobalTheory.CoverDeg.GoodCover p π D δ U → ∀ (W : X.Opens) (x : Fin D → Γ(X, W)), IsAffineOpen W → (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W) x).Etale → ∀ z : Y, π z ∈ U → π z ∈ W → ∃ V : Y.Opens, IsAffineOpen V ∧ z ∈ V ∧ ∃ h : V ≤ π ⁻¹ᵁ W, (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q V) (fun a => (π.appLE W V h).hom (x a))).Etale := by
  first | exact @GlobalTheory.CoverDeg.etale_pullback_coords | exact GlobalTheory.CoverDeg.etale_pullback_coords | (intros; apply GlobalTheory.CoverDeg.etale_pullback_coords <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.norm_scalarPoincareDetRatio_lact_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧ (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  first | exact @GlobalTheory.ScalarPoin.norm_qS_lact_le | exact GlobalTheory.ScalarPoin.norm_qS_lact_le | (intros; apply GlobalTheory.ScalarPoin.norm_qS_lact_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom := by
  first | exact @GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | exact GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | (intros; apply GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

theorem _root_.GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 → phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  first | exact @GlobalTheory.ScalarPoin.phla_laS_cpt | exact GlobalTheory.ScalarPoin.phla_laS_cpt | (intros; apply GlobalTheory.ScalarPoin.phla_laS_cpt <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

abbrev Bas : Type := {V : Z.affineOpens // ∃ i, V.1 ≤ W i}

abbrev incl : (Bas W)ᵒᵖ ⥤ AffOp Z :=
  (Monotone.functor (f := (Subtype.val : Bas W → Z.affineOpens)) fun _ _ h ↦ h).op

def resEquiv (hW : ⨆ i, W i = ⊤) : HO1 s ≃ₗ[R] CatCoh.H1 (incl W ⋙ OAff s) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s) (incl W)).pull1
    (GlobalTheory.CoverO.restrict_cover_affine_pull1_bijective R Z s J W hW)

def idx {W : J → Z.Opens} (V : Bas W) : J := V.2.choose

theorem le_idx {W : J → Z.Opens} (V : Bas W) : V.1.1 ≤ W (idx V) := V.2.choose_spec

theorem le_of_hom {W : J → Z.Opens} {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') : V'.unop.1.1 ≤ V.unop.1.1 :=
  leOfHom a.unop

def IsCocycle (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
    resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
      (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
      (c i i'')

def fc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : CatCoh.C1 (incl W ⋙ OAff s) :=
  fun V V' a ↦ resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
    (c (idx V.unop) (idx V'.unop))

theorem resG_resG' {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fc_mem {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) : fc s W c ∈ Z1 (incl W ⋙ OAff s) := by
  intro V V' V'' a b
  have hV'' : V''.unop.1.1 ≤ W (idx V.unop) ⊓ W (idx V'.unop) ⊓ W (idx V''.unop) :=
    le_inf (le_inf ((le_of_hom b).trans ((le_of_hom a).trans (le_idx V.unop)))
      ((le_of_hom b).trans (le_idx V'.unop))) (le_idx V''.unop)
  have e := congrArg (resG Z hV'') (hc (idx V.unop) (idx V'.unop) (idx V''.unop))
  simp only [map_add (f := _), resG_resG'] at e
  have key : resG Z (le_inf ((le_of_hom (a ≫ b)).trans (le_idx V.unop)) (le_idx V''.unop))
      (c (idx V.unop) (idx V''.unop)) =
      resG Z (le_of_hom b) (resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop))) +
      resG Z (le_inf ((le_of_hom b).trans (le_idx V'.unop)) (le_idx V''.unop))
        (c (idx V'.unop) (idx V''.unop)) := by
    rw [resG_resG']
    exact e.symm
  exact key

def cmp (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : HO1 s := by
  classical
  exact if h : fc s W c ∈ Z1 (incl W ⋙ OAff s) then
    (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, h⟩) else 0

theorem cmp_of_isCocycle (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    cmp s W hW c = (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, fc_mem s W hc⟩) := by
  unfold cmp
  rw [dite_eq_left (fc_mem s W hc)]

theorem restrict_cmp (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    (CoefMap.restrict (OAff s) (incl W)).pull1 (cmp s W hW c) =
      H1.mk _ ⟨fc s W c, fc_mem s W hc⟩ := by
  rw [cmp_of_isCocycle s W hW hc]
  exact (resEquiv s W hW).apply_symm_apply _

end GlobalTheory.CechCmp
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem mp_cochain_congr {p : ℕ} (c : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (h : s.1 = s'.1)
    {b : (NE κ)ᵒᵖ} (φ : ne s.1 (card_nonempty s) ⟶ b) (φ' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F φ (c s) = mp F φ' (c s') := by
  obtain rfl : s = s' := Subtype.ext h
  rw [Subsingleton.elim φ φ']

theorem orderedCech_cochainsZero_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0) : d0 F (e0 F c) = e1 F (δ F 0 c) := by
  funext a b f
  rw [amitsur_d0_apply]
  simp only [e0, e1, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply]
  rw [← mp_comp]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply]

    rw [δ_apply, map_sum]
    have hb : mn b ∈ ({mn b, mn a} : Finset κ) := by simp
    have ha : mn a ∈ ({mn b, mn a} : Finset κ) := by simp
    have s1 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn b) = 1 :=
      GlobalTheory.cubeSign_eq_one_of_forall_le (by simp [h.le])
    have s2 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn a) = -1 := by
      have := GlobalTheory.cubeSign_erase_of_lt (t := {mn b, mn a}) hb h
      rw [Finset.erase_insert (by simp [h.ne]), GlobalTheory.cubeSign_singleton] at this
      omega
    rw [Fintype.sum_eq_add (⟨mn b, hb⟩ : ({mn b, mn a} : Finset κ)) ⟨mn a, ha⟩
      (fun e => h.ne (congrArg Subtype.val e))
      (by
        rintro ⟨x, hx⟩ ⟨h1, h2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (h1 rfl).elim
        · exact (h2 rfl).elim)]
    simp only [s1, s2, one_smul, neg_smul, map_neg, ← mp_comp]
    rw [neg_add, neg_neg, neg_add_eq_sub]
    refine congrArg₂ (· - ·) ?_ ?_
    · refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn a, ha⟩) ?_ _ _
      show {mn b} = Finset.erase {mn b, mn a} (mn a)
      rw [Finset.pair_comm, Finset.erase_insert (by simp [h.ne'])]
    · refine mp_cochain_congr F c (s := ⟨{mn a}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn b, hb⟩) ?_ _ _
      show {mn a} = Finset.erase {mn b, mn a} (mn b)
      rw [Finset.erase_insert (by simp [h.ne])]
  · have e : mn b = mn a := le_antisymm (mn_le_of_hom f) (not_lt.1 h)
    rw [LinearMap.zero_apply, sub_eq_zero]
    refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
      (s' := ⟨{mn a}, Finset.card_singleton _⟩) ?_ _ _
    show ({mn b} : Finset κ) = {mn a}
    rw [e]

end GlobalTheory.CechPoset
end
end
