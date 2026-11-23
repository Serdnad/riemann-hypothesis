module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle157
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.LocalFields.PadicLogSeries
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle183
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle087
public import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.LocalFields.LocalFourierHaar
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.Tw.NormOneCore

theorem exists_normOne_mul_compact : ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K], (∀ x : K, ‖star x‖ = ‖x‖) → ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) K), GlobalTheory.Tw.Reg δ → ∀ C : Set (GL (Fin n) K), IsCompact C → ∃ D : Set (GL (Fin n) K), IsCompact D ∧ ∀ z : GL (Fin n) K, (z : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} → ∀ u ∈ C, (u : Matrix (Fin n) (Fin n) K) = (z : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (z : Matrix (Fin n) (Fin n) K) → ∃ t : GL (Fin n) K, (t : Matrix (Fin n) (Fin n) K) ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm δ} ∧ (t : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ (t : Matrix (Fin n) (Fin n) K) = 1 ∧ ∃ d ∈ D, z = t * d := by
  intro K _ _ _ hK n δ hδ C hC
  have hu := hδ.1
  set N := GlobalTheory.Tw.nrm δ with hNdef
  set A := Algebra.adjoin K {N} with hAdef
  letI : CommRing A := Algebra.instCommRingAdjoinSingleton N
  have hA := GlobalTheory.Tw.CentralizerAdjoin.adj_adjoin hu
  have hmul := GlobalTheory.Tw.CentralizerAdjoin.adj_mul' hu
  have hsemi := GlobalTheory.Tw.CentralizerAdjoin.adj_semi δ
  have hone := GlobalTheory.Tw.CentralizerAdjoin.adj_one' hu
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) K, GlobalTheory.Tw.adj δ (x + y) = GlobalTheory.Tw.adj δ x + GlobalTheory.Tw.adj δ y :=
    fun x y => by simpa using hsemi 1 x y
  have hzero : GlobalTheory.Tw.adj δ 0 = 0 := by simp [GlobalTheory.Tw.adj]
  let σ : A →+* A :=
    { toFun := fun x => ⟨GlobalTheory.Tw.adj δ x, (hA x x.2).1⟩
      map_one' := Subtype.ext hone
      map_mul' := fun x y => by
        apply Subtype.ext
        change GlobalTheory.Tw.adj δ (x.1 * y.1) = _
        rw [hmul]
        simpa only [Subalgebra.coe_mul] using congrArg Subtype.val (mul_comm (⟨_, (hA y y.2).1⟩ : A) ⟨_, (hA x x.2).1⟩)
      map_zero' := Subtype.ext hzero
      map_add' := fun x y => Subtype.ext (hadd x.1 y.1) }
  have hσv : ∀ x : A, (σ x : Matrix (Fin n) (Fin n) K) = GlobalTheory.Tw.adj δ x := fun x => rfl
  have hσσ : ∀ x : A, σ (σ x) = x := fun x => Subtype.ext (hA x x.2).2
  haveI : IsReduced A := ⟨fun x ⟨m, hm⟩ => Subtype.ext
    (GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable K n N hδ.2 x x.2 m (by simpa using congrArg Subtype.val hm))⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨e, f, he, hf, hes, hsum, hnull⟩ := GlobalTheory.T.reduced_artinian_involution_idempotent_split A σ hσσ

  have hse : σ e * f = 0 := by
    have h1 : σ e * σ e = σ e := by rw [← map_mul, he.eq]
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination (-1 : A) * h1 + (-1 : A) * hes
  have hef : e * f = 0 := by
    have : f = 1 - e - σ e := by rw [← hsum]; ring
    rw [this]; linear_combination -he.eq - hes
  have hσf : σ f = f := by
    have h := congrArg σ hsum
    rw [map_add (f := _), map_add (f := _), hσσ, map_one] at h
    linear_combination h - hsum
  letI : ContinuousStar K := ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, hK]).continuous⟩
  have hqc : Continuous fun w : Matrix (Fin n) (Fin n) K => w * GlobalTheory.Tw.adj δ w := by
    unfold GlobalTheory.Tw.adj
    fun_prop
  have hss : σ e * σ e = σ e := by rw [← map_mul, he.eq]
  let S : Submodule K (Matrix (Fin n) (Fin n) K) :=
    Submodule.map (LinearMap.mulRight K (f : Matrix (Fin n) (Fin n) K)) (Subalgebra.toSubmodule A)
  have hhom : ∀ (c : K) (w : Matrix (Fin n) (Fin n) K),
      (c • w) * GlobalTheory.Tw.adj δ (c • w) = (c * star c) • (w * GlobalTheory.Tw.adj δ w) := by
    intro c w
    have : GlobalTheory.Tw.adj δ (c • w) = star c • GlobalTheory.Tw.adj δ w := by simpa [hzero] using hsemi c w 0
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hnullS : ∀ w ∈ S, w * GlobalTheory.Tw.adj δ w = 0 → w = 0 := by
    intro w hw h0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
    have hx : (⟨a, ha⟩ * f : A) * σ (⟨a, ha⟩ * f) = 0 := Subtype.ext h0
    have h1 := hnull _ hx
    rw [mul_assoc, hf.eq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨B1, hB1, hB1m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * u) '' C)
    (hC.image (continuous_const.mul Units.continuous_val))
  obtain ⟨B2, hB2, hB2m⟩ := GlobalTheory.T.isCompact_preimage_quadratic_map_no_null_vectors K hK n S (fun w => w * GlobalTheory.Tw.adj δ w) hqc hhom hnullS
    ((fun u : GL (Fin n) K => (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) '' C)
    (hC.image (continuous_const.mul (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K))))
  let φ : GL (Fin n) K × Matrix (Fin n) (Fin n) K × Matrix (Fin n) (Fin n) K →
      Matrix (Fin n) (Fin n) K × (Matrix (Fin n) (Fin n) K)ᵐᵒᵖ := fun p =>
    ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * p.1 + p.2.1,
      MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((p.1⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + p.2.2))
  have hφ : Continuous φ :=
    ((continuous_const.add (continuous_const.mul (Units.continuous_val.comp continuous_fst))).add
      (continuous_fst.comp continuous_snd)).prodMk
      (MulOpposite.continuous_op.comp ((continuous_const.add
        (continuous_const.mul ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) K)).comp continuous_fst))).add
          (continuous_snd.comp continuous_snd)))
  refine ⟨Units.embedProduct _ ⁻¹' (φ '' (C ×ˢ (B1 ×ˢ B2))),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage ((hC.prod (hB1.prod hB2)).image hφ), ?_⟩
  intro z hz u hu' huz
  have hzi : ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∈ A := by
    rw [Matrix.coe_units_inv]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hz) (GlobalTheory.Tw.CentralizerAdjoin.inv_mem_adjoin_of_isUnit z.isUnit)
  set z' : A := ⟨z, hz⟩ with hz'
  set zi : A := ⟨_, hzi⟩ with hzi'
  have hz1 : z' * zi = 1 := Subtype.ext (Units.mul_inv z)
  have hsz1 : σ z' * σ zi = 1 := by rw [← map_mul, hz1, map_one]
  set tA : A := e * z' + σ e * σ zi + f with htA
  set tiA : A := e * zi + σ e * σ z' + f with htiA
  have hprod : tA * tiA = 1 := by
    rw [htA, htiA]
    linear_combination (z' * zi) * he.eq + e * hz1 + (z' * σ z' + σ zi * zi) * hes + (z' + zi) * hef +
      (σ zi * σ z') * hss + σ e * hsz1 + (σ zi + σ z') * hse + hf.eq + hsum
  have hprod' : tiA * tA = 1 := by rw [mul_comm]; exact hprod
  have hσt : σ tA = tiA := by
    rw [htA, htiA]; simp only [map_add (f := _), map_mul, hσσ, hσf]; ring
  let t : GL (Fin n) K := ⟨tA, tiA, congrArg Subtype.val hprod, congrArg Subtype.val hprod'⟩
  have hinvu : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * σ zi : A) : Matrix (Fin n) (Fin n) K) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [huz]
    exact congrArg Subtype.val (show (z' * σ z') * (zi * σ zi) = 1 by
      linear_combination (σ z' * σ zi) * hz1 + hsz1)
  refine ⟨t, tA.2, ?_, t⁻¹ * z, ?_, by simp⟩
  · show (tA : Matrix (Fin n) (Fin n) K) * GlobalTheory.Tw.adj δ tA = 1
    rw [← hσv, hσt]; exact congrArg Subtype.val hprod
  refine ⟨(u, (z : Matrix (Fin n) (Fin n) K) * f, ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f),
    ⟨hu', hB1m _ (Submodule.mem_map.mpr ⟨z, hz, rfl⟩) ⟨u, hu', ?_⟩,
      hB2m _ (Submodule.mem_map.mpr ⟨_, hzi, rfl⟩) ⟨u, hu', ?_⟩⟩, ?_⟩
  · show (f : Matrix (Fin n) (Fin n) K) * u = ((z' * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (z' * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [huz]
    exact congrArg Subtype.val (show f * (z' * σ z') = (z' * f) * σ (z' * f) by
      rw [map_mul, hσf]; linear_combination (-(z' * σ z')) * hf.eq)
  · show (f : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((zi * f : A) : Matrix (Fin n) (Fin n) K) * ((σ (zi * f) : A) : Matrix (Fin n) (Fin n) K)
    rw [hinvu]
    exact congrArg Subtype.val (show f * (zi * σ zi) = (zi * f) * σ (zi * f) by
      rw [map_mul, hσf]; linear_combination (-(zi * σ zi)) * hf.eq)
  · apply Prod.ext
    · show (e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K) + (z : Matrix (Fin n) (Fin n) K) * f = ((t⁻¹ * z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [huz]
      exact congrArg Subtype.val (show e + σ e * (z' * σ z') + z' * f = tiA * z' by
        rw [htiA]; linear_combination (-e) * hz1)
    · show MulOpposite.op ((e : Matrix (Fin n) (Fin n) K) + (σ e : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) + ((z⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * f) = MulOpposite.op (((t⁻¹ * z)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      rw [hinvu, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      exact congrArg MulOpposite.op (congrArg Subtype.val (show e + σ e * (zi * σ zi) + zi * f = zi * tA by
        rw [htA]; linear_combination (-e) * hz1))
end GlobalTheory.Tw.NormOneCore
end

section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma.InvAlg.ClRel

theorem eq_of_mk_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  intro K B x y h
  have hsu : ∀ u : B.Aˣ, B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have heq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [hu]
      calc (x.1 : B.A) = (x.1 : B.A) * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) *
            (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by rw [hsu, Units.mul_inv, one_mul, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]
      ring
  exact (heq.eqvGen_iff).mp (Quot.eqvGen_exact h)

end GlobalTheory.UnitLemma.InvAlg.ClRel
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.GramTwistNorm

open GlobalTheory.UnitLemma

theorem phi_map (a : ℕ) {R : Type} [CommRing R] (c : R →+* R) :
    (GlobalTheory.Tw.Phi a R).map c = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) :=
  _root_.UpperTheory.Reformulated.B.Yzd3.phi_mul_self a

theorem phi_mul_transpose (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 :=
  _root_.UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose a

theorem herm_sum_left {K : UQ} (B : InvAlg K) (β : B.A) {ι : Type} (s : Finset ι) (v : ι → K.E)
    (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by

  simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
  map_smul, smul_eq_mul]

theorem herm_sum_right {K : UQ} (B : InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι) (r : ι → K.E)
    (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by

  simp only [InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_det_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (β : B.Aˣ) {a : ℕ}
    (b : Module.Basis (Fin a) K.E B.A) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set y := ∑ i, v i • b i with hy
  have hy0 : y ≠ 0 := by
    intro hy'
    apply hv0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hy' i
  have hyb : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, herm_sum_left]
    exact this
  have hyz : ∀ z, B.herm β y z = 0 := by
    intro z
    rw [← b.sum_repr z, herm_sum_right]
    simp [hyb]
  have hβy : (β : B.A) * y = 0 := by
    apply GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hsep
    intro w
    have := hyz (B.σ w)
    simp only [InvAlg.herm, B.σ_σ] at this
    exact this
  exact hy0 ((Units.mul_right_eq_zero β).1 hβy)

theorem gram_map_conj {K : UQ} (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (hec : ∀ x, e (K.c x) = c (e x)) (a : ℕ) (β : B.A)
    (hβ : B.σ β = β * ((-1) ^ (a - 1) * B.g)) (b : Module.Basis (Fin a) K.E B.A) :
    ((Matrix.of fun i j => B.herm β (b i) (b j)).map e).map c =
      ((-1 : L) ^ (a - 1)) • (((Matrix.of fun i j => B.herm β (b i) (b j)).map e)ᵀ *
        (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e) :=
  _root_.GlobalTheory.ScalarSigmaBasis.main B L e c hec a β hβ b

theorem gram_twisted_norm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  intro K B L _ e c hec hcc a Q hPQ hQs hQd β hβ b
  set S : Matrix (Fin a) (Fin a) K.E := Matrix.of fun i j => B.herm β (b i) (b j) with hS
  have hG : (Matrix.of fun i j => e (B.herm β (b i) (b j))) = S.map e := rfl
  have hsep : B.P.Separable := by rw [hPQ]; exact hQs.map
  rw [hG]
  refine ⟨?_, ?_⟩
  · have hdet : (S.map e).det = e S.det := by
      rw [show S.map e = (e : K.E →+* L).mapMatrix S from rfl, ← RingHom.map_det]
      rfl
    rw [hdet, isUnit_iff_ne_zero]
    exact (map_ne_zero e).2 (gram_det_ne_zero B hsep β b)
  · intro δ hδ
    set G := S.map e with hGdef
    set P := (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e with hP
    set Φ := GlobalTheory.Tw.Phi a L with hΦ
    have hGc : G.map c = ((-1 : L) ^ (a - 1)) • (Gᵀ * P) := gram_map_conj B L e c hec a β hβ b
    have hinv : (δ⁻¹).val = Φ * Gᵀ := by
      have h1 : (δ.val * Φ)⁻¹ = Gᵀ := by rw [← hδ, Matrix.transpose_transpose]
      have hΦinv : Φ⁻¹ = Φᵀ := Matrix.inv_eq_right_inv (phi_mul_transpose a)
      rw [Matrix.mul_inv_rev, hΦinv, ← Matrix.coe_units_inv] at h1
      calc (δ⁻¹).val = Φ * Φᵀ * (δ⁻¹).val := by rw [hΦ, phi_mul_transpose, Matrix.one_mul]
        _ = Φ * Gᵀ := by rw [Matrix.mul_assoc, h1]
    have hθ : (thetaGL a c δ).val = Φ * ((δ⁻¹).val.map c)ᵀ * Φᵀ := rfl
    have hΦΦ : Φᵀ * Φᵀ = ((-1 : L) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) L) := by
      rw [← Matrix.transpose_mul, hΦ, phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
    have hδΦ : δ.val * Φ * Gᵀ = 1 := by rw [Matrix.mul_assoc, ← hinv, Units.mul_inv]
    have key : (δ * thetaGL a c δ).val = P := by
      rw [Units.val_mul, hθ, hinv, Matrix.map_mul, hΦ, phi_map, ← hΦ, Matrix.transpose_mul,
        Matrix.transpose_map, Matrix.transpose_transpose, hGc]
      calc δ.val * (Φ * ((-1 : L) ^ (a - 1) • (Gᵀ * P) * Φᵀ) * Φᵀ)
          = ((-1 : L) ^ (a - 1)) • ((δ.val * Φ * Gᵀ) * P * (Φᵀ * Φᵀ)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = P := by
            rw [hδΦ, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
              neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, hP, show (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e =
      (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map (e : K.E →+* L) from rfl,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    change B.P.map (e : K.E →+* L) = Q
    rw [hPQ, Polynomial.map_map]
    have : (e : K.E →+* L).comp e.symm.toRingHom = RingHom.id L := by
      ext x; simp
    rw [this, Polynomial.map_id]

end GlobalTheory.GramTwistNorm
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramChange

open GlobalTheory.UnitLemma

theorem herm_sum_sum (K : UQ) (B : InvAlg K) (β : B.A) {a : ℕ} (b : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (i j : Fin a) :
    B.herm β (∑ k, M k i • b k) (∑ l, M l j • b l) =
      ∑ k, ∑ l, M k i * B.herm β (b k) (b l) * K.c (M l j) := by
  have hσ : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  unfold InvAlg.herm

  simp only [map_sum, hσ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
  LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_of_sum (K : UQ) (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (he : ∀ x, e (K.c x) = c (e x)) {a : ℕ} (β : B.A) (b v : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (hv : ∀ j, v j = ∑ i, M i j • b i) :
    (Matrix.of fun i j => e (B.herm β (v i) (v j))) =
      (M.map e)ᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * (M.map e).map c := by
  ext i j

  simp only [Matrix.of_apply, hv, herm_sum_sum, Matrix.mul_apply, Matrix.transpose_apply,
  Matrix.map_apply, map_sum, map_mul, he, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  intro K B L _ e c he a β b
  refine ⟨fun P => ?_, fun b' => ?_⟩
  · set M : Matrix (Fin a) (Fin a) K.E := P.val.map e.symm with hM
    have hMe : M.map e = P.val := by
      ext i j; simp [hM]
    have hdet : IsUnit M.det := by
      have h1 : e M.det = P.val.det := by
        rw [← hMe]; exact RingHom.map_det (e : K.E →+* L) M
      have h2 : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      rw [← h1] at h2
      exact (isUnit_map_iff e _).mp h2
    refine ⟨b.map (Matrix.toLinearEquiv b M hdet), ?_⟩
    rw [gram_of_sum K B L e c he β b _ M, hMe]
    intro j
    simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · have hdet : IsUnit ((b.toMatrix b').map e).det := by
      have h1 : e (b.toMatrix b').det = ((b.toMatrix b').map e).det :=
        RingHom.map_det (e : K.E →+* L) _
      rw [← h1]
      exact (isUnit_map_iff e _).mpr (b.isUnit_det b')
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet.ne_zero, ?_⟩
    rw [gram_of_sum K B L e c he β b b' (b.toMatrix b')]
    · rfl
    · intro j; rw [b.sum_toMatrix_smul_self]

end GlobalTheory.GramChange
end

section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.FunExt GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LBCNu

open MeasureTheory

theorem distribHaarChar_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (z : k'ˣ) :
    distribHaarChar k (Units.map (Algebra.norm k : k' →* k) z) = distribHaarChar k' z := by
  let b := Module.finBasis k k'
  let e : k' ≃ₗ[k] (Fin (Module.finrank k k') → k) := b.equivFun
  let e' : k' ≃ₜ+ (Fin (Module.finrank k k') → k) :=
    { e.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  let M : k' ≃ₗ[k] k' := LinearEquiv.ofLinear (LinearMap.mulLeft k (z : k')) (LinearMap.mulLeft k ((z⁻¹ : k'ˣ) : k'))
    (by ext x; simp) (by ext x; simp)
  let Lz : (Fin (Module.finrank k k') → k) ≃ₗ[k] (Fin (Module.finrank k k') → k) := (e.symm.trans M).trans e
  have h1 : distribHaarChar (Fin (Module.finrank k k') → k) Lz = distribHaarChar k' z :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport e' z Lz (fun x => by
      show e ((z : k') * x) = e (M (e.symm (e x)))
      simp [M])
  rw [← h1, GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq]
  congr 1
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, LinearEquiv.coe_det, Lz, Algebra.norm_apply]
  symm
  show LinearMap.det (e.toLinearMap ∘ₗ M.toLinearMap ∘ₗ e.symm.toLinearMap) = _
  rw [LinearMap.det_conj]
  rfl


open GlobalTheory.SmGL GlobalTheory.SplitWeil in
theorem absPow_comp_norm {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k'] [IsModuleTopology k k'] (t : ℂ) :
    (absPow k t).comp (Units.map (Algebra.norm k : k' →* k)) = absPow k' t := by
  ext z
  simp only [MonoidHom.comp_apply, val_absPow, nabs, distribHaarChar_norm]

end GlobalTheory.LBCNu
end
