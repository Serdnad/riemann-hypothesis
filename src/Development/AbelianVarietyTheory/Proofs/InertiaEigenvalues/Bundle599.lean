module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle514
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle575
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle523
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle158
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle325
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle576
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle574
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eval_derivative_scaleRoots_mul {R : Type*} [CommRing R] (P : Polynomial R) (s x : R) :
    (Polynomial.derivative (P.scaleRoots s)).eval (s * x) =
      s ^ (P.natDegree - 1) * (Polynomial.derivative P).eval x := by
  apply GlobalTheory.Henselisation.eval_derivative_scaleRoots_mul <;> assumption

theorem exists_approx_root_scaleRoots {R : Type*} [CommRing R] (P : Polynomial R) (hP : 0 < P.natDegree)
    (t x b : R) (c : ℕ) (hb : P.eval x ∣ b * (Polynomial.derivative P).eval x - t ^ c) (n : ℕ) :
    ∃ (m : ℕ) (q : R), P.eval x ∣ q - t ^ m * x ∧ P.eval x ^ (n + 1) ∣ (P.scaleRoots (t ^ m)).eval q := by
  induction n with
  | zero => exact ⟨0, x, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, q, ⟨z, hz⟩, ⟨w, hw⟩⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, P.natDegree = e + 1 := ⟨P.natDegree - 1, by omega⟩
    obtain ⟨v, hv⟩ := hb
    set E := P.eval x with hE
    set s := t ^ m with hs
    set r := t ^ c * s ^ e with hr
    have hsr : t ^ (m + (c + m * e)) = s * r := by rw [hr, hs]; ring
    set h := -(b * (P.scaleRoots s).eval q) with hh
    refine ⟨m + (c + m * e), r * q + h, ?_, ?_⟩
    · rw [hsr]
      refine ⟨r * z - b * E ^ n * w, ?_⟩
      rw [hh, hw]
      linear_combination r * hz
    · rw [hsr]
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.scaleRoots (s * r)) (r * q) h
      have h0 : (P.scaleRoots (s * r)).eval (r * q) = r ^ (e + 1) * (P.scaleRoots s).eval q := by
        rw [Polynomial.scaleRoots_mul, Polynomial.scaleRoots_eval_mul, Polynomial.natDegree_scaleRoots, he]
      have h1 := eval_derivative_scaleRoots_mul P (s * r) x
      rw [he, Nat.add_sub_cancel] at h1
      obtain ⟨y, hy⟩ := Polynomial.sub_dvd_eval_sub (r * q) (s * r * x)
        (Polynomial.derivative (P.scaleRoots (s * r)))
      have h2 : (Polynomial.derivative (P.scaleRoots (s * r))).eval (r * q) =
          (s * r) ^ e * (Polynomial.derivative P).eval x + E * (r * z * y) := by
        rw [← h1]
        linear_combination hy + r * y * hz
      rw [hk, h0, h2, hh, hw]
      refine ⟨-((s * r) ^ e * v * w) - b * w * (r * z * y) + k * b ^ 2 * w ^ 2 * E ^ n, ?_⟩
      have h3 : r ^ (e + 1) = (s * r) ^ e * t ^ c := by
        rw [pow_succ, mul_pow]; nth_rewrite 2 [hr]; ring
      rw [h3]
      linear_combination (-((s * r) ^ e * E ^ (n + 1) * w)) * hv

theorem BK.exists_approx_root : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n : ℕ),
    ∃ (m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X ∧
      bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) := by
  intro l _ K bk n
  obtain ⟨c, a, b, hab⟩ := GlobalTheory.T.bezout_eisenstein_derivative_prime_pow l K bk
  have hcoe : ∀ p : Polynomial (Wq l bk.a),
      (p.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) = (p : bk.S) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_C_X_eq_coe]
  have hdeg : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).natDegree = bk.Ep.natDegree :=
    bk.monic.natDegree_map _
  have hb : (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S)).eval (X : bk.S) ∣
      (b : bk.S) * (Polynomial.derivative (bk.Ep.map (PowerSeries.C : Wq l bk.a →+* bk.S))).eval X -
        (l : bk.S) ^ c := by
    rw [Polynomial.derivative_map, hcoe, hcoe]
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hab
    beta_reduce at h
    rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C, map_pow, map_natCast] at h
    exact ⟨-(a : bk.S), by linear_combination h⟩
  obtain ⟨m, q, h1, h2⟩ := exists_approx_root_scaleRoots _ (hdeg ▸ bk.deg_pos) (l : bk.S) X b c hb n
  rw [hcoe] at h1 h2
  refine ⟨m, q, h1, (pow_dvd_pow _ n.le_succ).trans ?_⟩
  rw [← Polynomial.eval_map, Polynomial.map_scaleRoots _ _ _ (by rw [bk.monic.leadingCoeff, map_one]; exact one_ne_zero),
    map_pow, map_natCast]
  exact h2

end GlobalTheory.BSP
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_periodMatrix_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∃ Q : GL n (Bst P), ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ h
  obtain ⟨hdom, hreg, hu⟩ := stRegular l P AI ⟨T⟩
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] (Bst P) V n b
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hK0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) (Bst P) c = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) ⟨c, c.2.2⟩ :=
    fun c => rfl
  have hst : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P),
      stRep P ρ g y = TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap y := fun g y => rfl
  refine GlobalTheory.T.exists_periodMatrix_of_finrank_alt ℚ_[l] ↥(K0 K) (Bst P) ↥(GK K)
    (fun g => (actSt P (g : GQ l) : Bst P →+* Bst P)) n (fun g => LinearMap.toMatrix b b (ρ g))
    (fun g => ?_) (fun g c => ?_) (fun x x' hx hh => ?_) (fun x hx hh => hu K x hx hh)
    ((Dst P ρ).map e.toLinearMap) (fun x => ?_) ?_
  · have h1 : LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g⁻¹) = 1 := by
      rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]
    exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero
  · rw [hK0]
    exact actSt_algebraMap P g _ _ (mem_GK.mp g.2 _ c.2.1)
  · obtain ⟨c, hc, hc'⟩ := hreg K x x' hx hh
    exact ⟨⟨c, hc, c.2⟩, by rw [hK0]; exact hc'⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    have h1 : e y ∈ (Dst P ρ).map e.toLinearMap ↔ y ∈ Dst P ρ := by
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    rw [h1, mem_Dst]
    refine forall_congr' fun g => ?_
    rw [hst, ← e.injective.eq_iff, he]
    rfl
  · rw [LinearEquiv.finrank_map_eq, h, finrank_eq_card_basis b]

end GlobalTheory.PMon
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.continuousCocycle_of_semistable_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  first | exact @GlobalTheory.cocycle_of_st_coboundary | exact GlobalTheory.cocycle_of_st_coboundary | (intros; apply GlobalTheory.cocycle_of_st_coboundary <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isPst_resTo_iff_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) :
    IsPst P (resTo ρ hK) ↔ IsPst P ρ := by
  let e : DpstUr P (resTo ρ hK) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x =>
        toUr P ρ ⟨((toUr P _).symm x).1, (Dpst_resTo P ρ hK).le ((toUr P _).symm x).2⟩
      invFun := fun x =>
        toUr P _ ⟨((toUr P ρ).symm x).1, (Dpst_resTo P ρ hK).ge ((toUr P ρ).symm x).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [IsPst, IsPst, e.rank_eq]

theorem finrank_le_finrank_DpstUr_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (hS : IsSst P ρ) :
    finrank ℚ_[l] V ≤ finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc

    rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    rw [show finrank ℚ_[l] ↥(Dst P ρ) = _ from hS, mul_comm]
  have h3 : finrank ℚ_[l] V ≤ Fintype.card ↥b :=
    Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  exact h3.trans hli.fintype_card_le_finrank

theorem isPst_of_isSst_resTo : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  intro l _ P AI T K K' hK V _ _ _ ρ hS
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg (resTo ρ hK)
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hK)) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt Cardinal.natCast_lt_aleph0)
  rw [← isPst_resTo_iff_padic P hK ρ, GlobalTheory.Pst.isPst_iff]
  refine ⟨inferInstance, le_antisymm ?_ (finrank_le_finrank_DpstUr_of_isSst P _ hS)⟩
  rw [← finrank_eq_rank] at hup
  exact_mod_cast hup

end GlobalTheory.PMon

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.galois_factor_tilt_log_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  first | (exact @GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (exact GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log) | (intros; apply GlobalTheory.InertiaEigenvalues.TiltGalLog.gal_factor_log  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem stInv_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔
      ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  intro l _ P AI T K x
  constructor
  · intro h
    obtain ⟨hdom, h2, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
    haveI := hdom
    obtain ⟨c, hcK, hc⟩ := h2 K 1 x one_ne_zero fun g => by rw [map_one, h g, one_mul]
    have hmem : (c : Om l) ∈ K0 K := IntermediateField.mem_inf.2 ⟨hcK, c.2⟩
    refine ⟨⟨c, hmem⟩, ?_⟩
    rw [hc, mul_one, Polynomial.algebraMap_apply]
    rfl
  · rintro ⟨c, rfl⟩ g
    have hc : (c : Om l) ∈ (K.1 : IntermediateField ℚ_[l] (Om l)) := (IntermediateField.mem_inf.1 c.2).1
    have hg : (g : GQ l) (c : Om l) = (c : Om l) := (mem_fixingSubgroup_iff _).1 g.2 _ hc
    have hK0 : algebraMap ↥(K0 K) P.R.B c =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, (IntermediateField.mem_inf.1 c.2).2⟩ := rfl
    rw [actSt]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, stHom_apply, Polynomial.map_C, Polynomial.C_comp]
    congr 1
    rw [hK0]
    exact P.actQ_Kur _ _ _ hg

end GlobalTheory.PMon
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormOneTwist

variable {D : D7}

def quotC (D : D7) : (AE D)ˣ →* (AE D)ˣ :=
  MonoidHom.id _ / Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def finQuot (D : D7) : (AE D)ˣ →* (GlobalTheory.FinalJoin.AfE D)ˣ :=
  (Units.map (finPart D).toMonoidHom).comp (quotC D)

theorem finPart_mul_inv (x : (AE D)ˣ) :
    finPart D (x : AE D) * finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
  rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]

theorem finQuot_val (x : (AE D)ˣ) :
    ((finQuot D x : (GlobalTheory.FinalJoin.AfE D)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      finPart D (x : AE D) * sigR (Af D.host.F) D.sp.cm.sig (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) := by
  show finPart D ((x : AE D) * sigR (AF D.host.F) D.sp.cm.sig ((x⁻¹ : (AE D)ˣ) : AE D)) = _
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]

theorem normOne_finQuot (x : (AE D)ˣ) : GlobalTheory.FinalJoin.NormOne (finQuot D x) := by
  change _ * sigR (Af D.host.F) D.sp.cm.sig _ = 1
  rw [finQuot_val]
  exact GlobalTheory.DetOnto.norm_one _ (GlobalTheory.DetOnto.sigR_sigR D) (finPart_mul_inv x)

theorem finQuot_of_isDetRoot {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetRoot V g x) :
    finQuot D x = Matrix.GeneralLinearGroup.det (finHom V g) := by
  apply Units.ext
  have h1 := congrArg (finPart D) hx
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR] at h1
  rw [finQuot_val, h1, mul_assoc, ← RingHom.map_mul, finPart_mul_inv x, RingHom.map_one, mul_one,
    GlobalTheory.DetRootChar.finPart_det]

theorem finQuot_incA (e : D.host.Eˣ) :
    ((finQuot D (Units.map (incA D).toMonoidHom e) : (GlobalTheory.FinalJoin.AfE D)ˣ) : GlobalTheory.FinalJoin.AfE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((e : D.host.E) * D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) := by
  rw [finQuot_val]
  show finPart D (incA D (e : D.host.E)) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (incA D ((e⁻¹ : D.host.Eˣ) : D.host.E))) = _
  show ((1 : Af D.host.F) ⊗ₜ[D.host.F] (e : D.host.E)) *
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end GlobalTheory.NormOneTwist

namespace GlobalTheory.NormOneTwist

variable {D : D7}

end GlobalTheory.NormOneTwist
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_teichmuller_log_unit_bcris : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  first | (exact @GlobalTheory.LogU.exists_log_unit) | (exact GlobalTheory.LogU.exists_log_unit) | (intros; apply GlobalTheory.LogU.exists_log_unit  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_bdRPlus_lattice_generators_ddR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  first | exact @GlobalTheory.BdRLatticeGens.exists_lattice_generators | exact GlobalTheory.BdRLatticeGens.exists_lattice_generators | (intros; apply GlobalTheory.BdRLatticeGens.exists_lattice_generators <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | exact GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | (intros; apply GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices


theorem _root_.GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (Jumps (PD := (D.loc l).PD K) T).Finite := by
  first | exact @GlobalTheory.NL.JumpsFinite.jumps_finite | exact GlobalTheory.NL.JumpsFinite.jumps_finite | (intros; apply GlobalTheory.NL.JumpsFinite.jumps_finite <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ Fs : Finset (↥(OL LL))ˣ, (∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → uU W ^ (-(a + j)) ∈ Fs) → ∀ x ∈ invN W T (W.Q ^ y), Polynomial.aeval (W.γ T) (∏ c ∈ Fs, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x ∈ W.N T := by
  first | exact @GlobalTheory.NL.KillLevels.annihilate | exact GlobalTheory.NL.KillLevels.annihilate | (intros; apply GlobalTheory.NL.KillLevels.annihilate <;> assumption)
end
