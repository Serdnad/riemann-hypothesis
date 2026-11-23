module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle023
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle054
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle022
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedFormLaws

theorem sum_mul_left {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * (x.map fun z => t * z) d a) =
      t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem sum_mul_right {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (t : A) (x y : Matrix (Fin m) (Fin n) A) :
    (∑ a, ∑ b, ∑ e, ∑ d, P a b * c ((y.map fun z => t * z) e b) * Q e d * x d a) =
      c t * ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a := by
  simp only [Finset.mul_sum, Matrix.map_apply, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

variable {D : D7} {S T : HSp D}

theorem hO_mul_left (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T (x.map fun z => t * z) y = t * hO S T x y :=
  sum_mul_left (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_mul_right (t : Formalism.L2.Theta.AE D) (x y : WO S T) :
    hO S T x (y.map fun z => t * z) = cA D t * hO S T x y :=
  sum_mul_right (cA D) (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) t x y

theorem hO_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    hO S T (M.map (incA D)) (N.map (incA D)) = incA D (GlobalTheory.LatVac.hRat S T M N) := by
  unfold hO GlobalTheory.LatVac.hRat

  simp only [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, map_sum, RingHom.map_mul]

theorem symplOH_rat (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (M.map (incA D)) (N.map (incA D)) = algebraMap D.host.F (AF D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat S T M N)) := by
  have h2 : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun x => rfl
  rw [symplOH, symplO, hO_rat, ← RingHom.map_mul, h2, GlobalTheory.LatVac.trace_tmul, one_mul, RingHom.map_mul]

theorem hO_half (e : Formalism.L2.Theta.AE D) (u : WO S T) (he : e * cA D e = 0) (hu : IsHalf e u) : hO S T u u = 0 := by
  have h : (u.map fun z => e * z) = u := by
    funext i j
    exact hu i j
  have h1 := hO_mul_left e u u
  have h2 := hO_mul_right e u u
  rw [h] at h1 h2
  rw [h1, h2, ← mul_assoc, he, zero_mul]

theorem symplOH_laws : ∀ (D : D7) (S T : HSp D), (∀ x y z : WO S T, symplOH S T (x + y) z = symplOH S T x z + symplOH S T y z) ∧ (∀ x y z : WO S T, symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z) ∧ (∀ x : WO S T, symplOH S T x x = 0) ∧ (∀ x y : WO S T, symplOH S T x y + symplOH S T x y = symplO S T x y) ∧ Continuous (fun q : WO S T × WO S T => symplOH S T q.1 q.2) ∧ (∀ g ∈ ratL T S, ∀ g' ∈ ratL T S, ∃ a : D.host.F, symplOH S T g g' = algebraMap D.host.F (AF D.host.F) a) ∧ (∀ (a : AE D) (x y : WO S T), symplOH S T (x.map fun z => a * z) y = symplOH S T x (y.map fun z => cA D a * z)) ∧ (∀ (e a : AE D) (u : WO S T), e * cA D e = 0 → IsHalf e u → symplOH S T (u.map fun z => a * z) u = 0) ∧ ∀ x y : WO S T, x.map (finPart D) = 0 → y.map (infPart D) = 0 → symplOH S T x y = 0 := by
  intro D S T
  refine ⟨GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_self,
    fun x y => ?_, GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd, ?_, fun a x y => ?_,
    fun e a u he hu => ?_, fun x y hx hy => (GlobalTheory.OrientedHeis.symplOH_fin_real hy hx).2⟩
  · unfold symplOH
    rw [← add_mul, ← RingHom.map_add (f := _), add_halves, RingHom.map_one, one_mul]
  · rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
    exact ⟨_, symplOH_rat M N⟩
  · unfold symplOH symplO
    rw [hO_mul_left, hO_mul_right, GlobalTheory.DualPairCheck.cA_cA]
  · unfold symplOH symplO
    rw [hO_mul_left, hO_half e u he hu, mul_zero, mul_zero, LinearMap.map_zero, mul_zero]

end GlobalTheory.OrientedFormLaws
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem hasseNormSt : GlobalTheory.Published.HasseNormSt := by
  intro F _ _ δ x hδ hx hreal hfin
  classical
  by_cases hsq : IsSquare δ
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare hδ hsq x
  obtain ⟨S, -, hS⟩ := exists_superset_mem_sUnits F {Units.mk0 δ hδ, Units.mk0 x hx} ∅
  obtain ⟨T, hST, hT⟩ := exists_admissible_superset_finite_places F S
  have hδT : Units.mk0 δ hδ ∈ sUnits F T := hS T hST _ (by simp)
  have hxT : Units.mk0 x hx ∈ sUnits F T := hS T hST _ (by simp)
  have hloc : Units.mk0 x hx ∈ locNorm F ((Units.mk0 δ hδ : Fˣ) : F) T := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun _ => ?_
      rw [mem_normSub]
      exact hfin v
    · refine Subgroup.mem_iInf.mpr fun σ => ?_
      rw [mem_normSub]
      exact hreal σ
  have h := GlobalTheory.T.sUnit_mem_globalNorm_of_mem_localNorms F (Units.mk0 δ hδ) T hT hδT hsq _ hxT hloc
  rw [mem_normSub] at h
  exact h

end GlobalTheory.QNorm
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.SymplecticOrthogonalSesquilinear

theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_eq_neg {F R : Type} [Field F] [CharZero F] [CommRing R] [Algebra F R] {a : R} (h : a = -a) :
    a = 0 := by
  have h2 : (2 : F) • a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
  exact (smul_eq_zero_iff_right two_ne_zero).1 h2

theorem map_sesq {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) (c : A →+* A) (s : E → E)
    (hc : ∀ e, c (ι e) = ι (s e)) {m n : ℕ} (ξ : E) (P : Fin m → Fin m → E) (Q : Fin n → Fin n → E)
    (x y : Fin n → Fin m → E) :
    ι ξ * ∑ a, ∑ b, ∑ c', ∑ d, ι (P a b) * c (ι (y c' b)) * ι (Q c' d) * ι (x d a) =
      ι (ξ * ∑ a, ∑ b, ∑ c', ∑ d, P a b * s (y c' b) * Q c' d * x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem symplO_rat (D : D7) (S T : HSp D) (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  have h : ∃ e : D.host.E, incA D D.host.xi0 * hO S T (ratW T S γ) (ratW T S γ') = incA D e :=
    ⟨_, map_sesq (incA D) (cA D) star GlobalTheory.DualPairCheck.cA_incA D.host.xi0 (fun a b => S.gram⁻¹ a b)
      (fun a b => T.gram a b) γ γ'⟩
  obtain ⟨e, he⟩ := h
  refine ⟨Algebra.trace D.host.F D.host.E e, ?_⟩
  unfold symplO
  rw [he]
  exact trace_one_tmul _ e

theorem symplO_alt : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  intro D S T
  refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun x y => GlobalTheory.WeilVacMove.symplO_skew S T y x,
    fun x => eq_zero_of_eq_neg (F := D.host.F) (GlobalTheory.WeilVacMove.symplO_skew S T x x), symplO_rat D S T⟩
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
  · unfold symplO hO
    simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.SymplecticOrthogonalSesquilinear
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharFin

theorem finite_order_of_small {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [TopologicalSpace R] [TopologicalSpace A] [TopologicalSpace B] [ContinuousAdd B]
    (p : R →+* A) (q : R →+* B) (s : A × B → R) (hs : Continuous s) (hsz : ∀ z, s (p z, q z) = z)
    (S : Subring B) (hsmall : ∀ W ∈ 𝓝 (0 : B), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ S, N • y ∈ W)
    (hfin : ∀ N : ℕ, 0 < N → Finite (S ⧸ Ideal.span {(N : S)}))
    (χ : Rˣ →* Circle) (hχ : Continuous χ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) →
      (∃ y ∈ S, q x - 1 = N • y) → χ x = 1) ∧
      ∃ m : ℕ, 0 < m ∧ ∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) → χ x ^ m = 1 := by
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Rˣ) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  let f : B → R := fun b => s (1, 1 + b)
  have hf : Continuous f := hs.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hf0 : f 0 = 1 := by simpa [f] using hsz 1
  have h1 : f ⁻¹' T1 ∈ 𝓝 (0 : B) := hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hT1)
  have h2 : (fun b => MulOpposite.op (f b)) ⁻¹' T2 ∈ 𝓝 (0 : B) :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, hf0]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := hsmall _ (Filter.inter_mem h1 h2)
  have hpinv : ∀ x : Rˣ, p x = 1 → p (x⁻¹ : Rˣ) = 1 := fun x hx => by
    have := congrArg p x.mul_inv
    rwa [map_mul, hx, one_mul, map_one] at this
  let G : Subgroup Rˣ :=
    { carrier := {x | p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by simp [hx.1, hy.1], ?_, ?_⟩
        · rw [Units.val_mul, map_mul]; exact mul_mem hx.2.1 hy.2.1
        · rw [mul_inv, Units.val_mul, map_mul]; exact mul_mem hx.2.2 hy.2.2
      inv_mem' := fun {x} hx => ⟨hpinv x hx.1, hx.2.2, by simpa using hx.2.1⟩ }
  let ψ : G →* S :=
    { toFun := fun x => ⟨q (x : Rˣ), x.2.2.1⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  let φ : G →* (S ⧸ Ideal.span {(N : S)})ˣ :=
    ((Ideal.Quotient.mk (Ideal.span {(N : S)})).toMonoidHom.comp ψ).toHomUnits
  have hφ : ∀ x : G, φ x = 1 ↔ ∃ y ∈ S, q (x : Rˣ) - 1 = N • y := by
    intro x
    have : φ x = 1 ↔ Ideal.Quotient.mk (Ideal.span {(N : S)}) (ψ x) = Ideal.Quotient.mk _ 1 := by
      rw [Units.ext_iff]; rfl
    rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by simpa [ψ] using congrArg Subtype.val hy⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ] using h)⟩
  have hfx : ∀ x : G, φ x = 1 → ∃ y ∈ S, ((x : Rˣ) : R) = f (N • y) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := (hφ x).1 hx
    refine ⟨y, hy, ?_⟩
    have := hsz (x : Rˣ)
    rw [x.2.1] at this
    simp only [f, ← h, add_sub_cancel, this]
  have harc : ∀ x : G, φ x = 1 → χ x ∈ Circle.centeredArc (Real.pi / 2) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hfx x hx
    obtain ⟨y', hy', h'⟩ := hfx x⁻¹ (by rw [map_inv, hx, inv_one])
    refine hTV (hTT ⟨?_, ?_⟩)
    · change ((x : Rˣ) : R) ∈ T1
      rw [h]; exact (hNW y hy).1
    · change MulOpposite.op (((x⁻¹ : G) : Rˣ) : R) ∈ T2
      rw [h']; exact (hNW y' hy').2
  have hker : ∀ x : G, φ x = 1 → χ x = 1 := by
    intro x hx
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have := harc (x ^ n) (by rw [map_pow, hx, one_pow])
    rwa [Subgroup.coe_pow, map_pow] at this
  haveI := hfin N hN
  refine ⟨N, hN, fun x hx h => hker ⟨x, hx⟩ ((hφ _).2 h),
    Nat.card (S ⧸ Ideal.span {(N : S)})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have := hker ((⟨x, hx⟩ : G) ^ Nat.card (S ⧸ Ideal.span {(N : S)})ˣ)
    (by rw [map_pow, pow_card_eq_one'])
  rwa [Subgroup.coe_pow, map_pow] at this

open GlobalTheory.AdLat

section Integral

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' := fun hx hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) hx hy

theorem exists_int_add_nsmul (N : ℕ) (hN : 0 < N) (z : RA F E)
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ (x : 𝓞 E), ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + N • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hz
    obtain ⟨r, b, hb, rfl⟩ := (strong_approximation_mod_nat F N hN).2 a ha
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r * x, _, tmul_mem_adelicCompletion_of_integral F hb ⟨x, rfl⟩, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one (r : F),
      TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    obtain ⟨y, w, hw, rfl⟩ := hy
    refine ⟨x + y, u + w, add_mem hu hw, ?_⟩
    rw [show ((x + y : 𝓞 E) : E) = (x : E) + y from rfl, TensorProduct.tmul_add, smul_add]; abel
  | neg x _ hx =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    refine ⟨-x, -u, neg_mem hu, ?_⟩
    rw [show ((-x : 𝓞 E) : E) = -(x : E) from rfl, TensorProduct.tmul_neg, smul_neg]; abel

theorem finite_quotient_hatRing (N : ℕ) (hN : 0 < N) :
    Finite (hatRing F E ⧸ Ideal.span {(N : hatRing F E)}) := by
  let ι : 𝓞 E →+* hatRing F E :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F)
      (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _
      fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)})
    (Ideal.span {(N : hatRing F E)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : hatRing F E)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := exists_int_add_nsmul F E N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : RA F E) - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) = ((N : hatRing F E) : RA F E) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

end Integral

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_finUnit_finite_order : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  intro D χ hχ
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (RA D.host.F D.host.E) := ⟨rfl⟩
  haveI : ContinuousAdd (RA D.host.F D.host.E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) _
  have hsmall := (OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (by simp)).2
  have := finite_order_of_small (infPart D) (finPart D) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (hatRing D.host.F D.host.E) hsmall (finite_quotient_hatRing D.host.F D.host.E) χ hχ
  unfold FinUnit
  rw [integralFiniteAdeles_eq_adelicCompletion_integers]
  exact this

end GlobalTheory.CharFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    GlobalTheory.T.adelic_pair_reduced_basis F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := GlobalTheory.T.exists_isQGroup_weilRestriction_alt F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, GlobalTheory.T.glFreeAlgebraEmb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem _root_.GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational : ∀ (D : D7) (S T : HSp D), (∀ x x' y : WO S T, symplO S T (x + x') y = symplO S T x y + symplO S T x' y) ∧ (∀ x y y' : WO S T, symplO S T x (y + y') = symplO S T x y + symplO S T x y') ∧ (∀ x y : WO S T, symplO S T x y = -symplO S T y x) ∧ (∀ x : WO S T, symplO S T x x = 0) ∧ ∀ γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ a : D.host.F, symplO S T (ratW T S γ) (ratW T S γ') = algebraMap D.host.F (AF D.host.F) a := by
  first | exact @GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | exact GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt | (intros; apply GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt <;> assumption)

end
end
