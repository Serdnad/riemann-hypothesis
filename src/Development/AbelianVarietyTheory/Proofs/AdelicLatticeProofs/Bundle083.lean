module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle082
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle035
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacuumO
open GlobalTheory.FockCompare

variable {D : D7}

theorem map_fin_add {m n : ℕ} {x y : Mx D m n} (hx : x.map (finPart D) = 0) (hy : y.map (finPart D) = 0) :
    (x + y).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have e2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show finPart D (x i j + y i j) = 0
  rw [RingHom.map_add (f := _), e1, e2, add_zero]

theorem map_fin_neg {m n : ℕ} {x : Mx D m n} (hx : x.map (finPart D) = 0) : (-x).map (finPart D) = 0 := by
  funext i j
  have e1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show finPart D (-x i j) = 0
  rw [RingHom.map_neg, e1, neg_zero]

def thick {m n : ℕ} (Λ : AddSubgroup (Mx D m n)) (N : ℕ) : AddSubgroup (Mx D m n) where
  carrier := {x | ∃ l ∈ Λ, (x - N • l).map (finPart D) = 0}
  zero_mem' := ⟨0, Λ.zero_mem, by
    funext i j
    show finPart D (((0 : Mx D m n) - N • (0 : Mx D m n)) i j) = 0
    rw [nsmul_zero, sub_zero]
    exact RingHom.map_zero _⟩
  add_mem' := by
    rintro x y ⟨l, hl, hx⟩ ⟨l', hl', hy⟩
    refine ⟨l + l', Λ.add_mem hl hl', ?_⟩
    have e : x + y - N • (l + l') = (x - N • l) + (y - N • l') := by rw [nsmul_add]; abel
    rw [e]
    exact map_fin_add hx hy
  neg_mem' := by
    rintro x ⟨l, hl, hx⟩
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have e : -x - N • (-l) = -(x - N • l) := by rw [neg_nsmul]; abel
    rw [e]
    exact map_fin_neg hx

theorem piW_eq_zero (θ : InfFam D) (S T : HSp D) {u : WO S T} (hu : u.map (infPart D) = 0) : piW θ T S u = 0 := by
  funext τ i j
  have e : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [e, RingHom.map_zero]

theorem lineAt_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (v : RW T S) (h1 : v τ = z) (h2 : ∀ τ', τ' ≠ τ → v τ' = 0) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • v) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hσ.inf _ _ τ z)
  refine hσ.real_ext (V := T) (W := S) (hL.2.1 t) (hσ.real_iota T S _) ?_
  rw [hσ.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases h : τ' = τ
  · rw [if_pos h, h, Pi.smul_apply, h1]
    funext i j
    exact (Complex.real_smul).symm
  · rw [if_neg h, Pi.smul_apply, h2 τ' h, smul_zero]
    rfl

theorem exists_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) :
    ∃ f : WO S T → ℂ, f ≠ 0 ∧ ∀ c : ℂ, IsThetaFunO ψ S T (fun w => c * f w) ∧
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) (fun w => c * f w) ∧
      ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (fun w => c * f w) := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨om, J, hom, hJ, halt, hJJ, hsym, hpos⟩ := GlobalTheory.T.exists_realPlace_symplecticForm_positiveComplexStructure D ψ θ S T sS sT hψ hθ hS hT
  obtain ⟨aL, aR, a0, -, acont, arat, -, -, -⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  obtain ⟨hinf, χ, c0, c1, c2, c3, c4, c5⟩ := GlobalTheory.T.exists_semicharacter_completedSelfDualLattice D S T ΛS ΛT ψ hψ dS dT
  have htop : IsTopologicalAddGroup (WO S T) := (GlobalTheory.AdelicMatrixLattice.lattice D T S).1
  set Λ : AddSubgroup (WO S T) := latO S T ΛS ΛT fun _ => True with hΛ
  have hp2 : ∀ u ∈ Λ, piW θ T S (2 • u) = 0 := fun u hu => by
    rw [map_nsmul, piW_eq_zero θ S T (hinf u hu), smul_zero]
  have hlev : ∀ u ∈ thick Λ 2, ∃ l ∈ Λ, u - iotaW σ T S (piW θ T S u) = 2 • l := by
    rintro u ⟨l, hl, hu⟩
    refine ⟨l, hl, ?_⟩
    have e := hσ.iota_pi (V := T) (W := S) (x := u - 2 • l) hu
    rw [map_sub, hp2 l hl, sub_zero] at e
    rw [e]
    abel
  obtain ⟨f, f0, fc, fq, fl, fs, fv⟩ := GlobalTheory.T.continuous_bicharacter_weil_setup (WO S T) (RW T S) (piW θ T S) (iotaW σ T S)
    (fun x y => ψ (symplOH S T x y)) om J (ratL T S) (thick Λ 1) (thick Λ 2) χ
    (continuous_pi' hθ T S) (hσ.continuous_iota T S) (hσ.pi_iota T S)
    (fun x y z => by simp only [aL, AddChar.map_add_eq_mul])
    (fun x y z => by simp only [aR, AddChar.map_add_eq_mul])
    (fun x => by simp only [a0, AddChar.map_zero_eq_one])
    (fun x y => hψ.1.2.1 _) (hψ.1.1.comp acont)
    (fun x v => by
      have e := hom x (iotaW σ T S v) (hσ.real_iota T S v)
      rw [hσ.pi_iota] at e
      exact e)
    halt hJJ hsym hpos
    (fun g hg g' hg' => by
      obtain ⟨a, ha⟩ := arat g hg g' hg'
      simp only [ha]
      exact hψ.1.2.2.1 a)
    (by
      rintro _ ⟨g, rfl⟩ h
      have : g = 0 := by
        funext i j
        have e : θ (D.eTau.symm 1) (infPart D (incA D (g i j))) = 0 :=
          congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
        rw [comp_incA hθ] at e
        exact (tauE D _).injective (e.trans (RingHom.map_zero _).symm)
      rw [this, map_zero])
    (fun v => ⟨0, Λ.zero_mem, by rw [nsmul_zero, sub_zero]; exact hσ.real_iota T S v⟩)
    (fun R => by
      refine ((GlobalTheory.T.finite_rational_points_completed_lattice D S T ΛS ΛT dS dT R).image (ratW T S)).subset ?_
      rintro _ ⟨⟨g, rfl⟩, ⟨l, hl, h1⟩, h2⟩
      refine ⟨g, ⟨⟨l, hl, ?_⟩, fun τ i j => ?_⟩, rfl⟩
      · rw [one_nsmul] at h1
        exact h1
      · rw [← comp_incA hθ]
        let y : RW T S := piW θ T S (ratW T S g)
        exact ((norm_le_pi_norm (y τ i) j).trans ((norm_le_pi_norm (y τ) i).trans (norm_le_pi_norm y τ))).trans h2)
    (fun x hx => c0 x fun ⟨l, hl, h⟩ => hx ⟨l, hl, by rw [one_nsmul]; exact h⟩)
    c1 c2 (fun x v => c3 x _ (hσ.real_iota T S v))
    (GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos)
    (fun u hu x => by
      obtain ⟨l, hl, e⟩ := hlev u hu
      rw [e]
      exact c4 l hl x)
  have hh : ∀ (c : ℂ) (u : WO S T), piW θ T S u = 0 → (∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x) →
      heisO ψ S T u (fun w => c * f w) = fun w => c * f w := fun c u h1 h2 => by
    funext w
    show ψ (symplOH S T w u) * (c * f (w + u)) = c * f w
    rw [mul_left_comm, ← fl u h1 h2 w]
  refine ⟨f, f0, fun c => ⟨⟨fun g w => ?_, ⟨thick Λ 2, GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic D S T ΛS ΛT dS dT 2 two_pos, fun u hu h => ?_⟩,
    continuous_const.mul fc, fun k L hL hL0 w => ?_⟩, ⟨fun u hu => hh c _ (hp2 u hu) (c4 u hu),
      fun e he u hu h => hh c u (piW_eq_zero θ S T (hinf u hu)) (c5 e he u hu h)⟩, fun τ z => ?_⟩⟩
  · have e : ψ (symplOH S T (ratW T S g) w) * f (ratW T S g + w) = f w := fq (ratW T S g) ⟨g, rfl⟩ w
    show c * f (ratW T S g + w) = _ * (c * f w)
    rw [← e, mul_left_comm, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨l, hl, e⟩ := hlev u hu
    rw [piW_eq_zero θ S T h, map_zero, sub_zero] at e
    rw [e]
    exact hh c _ (hp2 l hl) (c4 l hl)
  · exact contDiff_const.mul (((smooth_iff_sm_and_real_lines D θ σ hσ T S).1 f).2 fs k L hL hL0 w)
  · funext w
    let v : RW T S := Pi.single τ z
    have v1 : v τ = z := Pi.single_eq_same _ _
    have v2 : ∀ τ', τ' ≠ τ → v τ' = 0 := fun τ' h => Pi.single_eq_of_ne h _
    have l1 := lineAt_eq hσ S T τ z v v1 v2
    have l2 := lineAt_eq hσ S T τ (cplxO (sS τ) (sT τ) z) (J v) (by rw [hJ, v1]) (fun τ' h => by
      rw [hJ, v2 τ' h]
      have : cplxO (sS τ') (sT τ') (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by simp [cplxO]
      exact this)
    have e := fv w v
    show deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ z t)) * (c * f (w + lineAt θ τ z t))) 0 +
      Complex.I * deriv (fun t : ℝ => ψ (symplOH S T w (lineAt θ τ (cplxO (sS τ) (sT τ) z) t)) *
        (c * f (w + lineAt θ τ (cplxO (sS τ) (sT τ) z) t))) 0 = 0
    simp only [l1, l2, mul_left_comm _ c, deriv_const_mul_field']
    rw [← mul_add]
    exact mul_eq_zero_of_right c e

theorem vacExists : ∀ D : D7, VacExistsO D := by
  intro D ψ θ hψ hθ S T sS sT _ _ hS hT ΛS ΛT dS dT
  obtain ⟨f, f0, hf⟩ := exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

end GlobalTheory.VacuumO
end
end

section

open Matrix

namespace GlobalTheory.VacuumLine

theorem exists_coord {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (J : U →ₗ[ℝ] U) (hJ : ∀ x, J (J x) = -x) :
    ∃ (g : ℕ) (e : U ≃ₗ[ℝ] (Fin g → ℂ)), ∀ v, e (J v) = Complex.I • e v := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ U := Complex.liftAux (J : Module.End ℝ U) (by ext x; simp [hJ])
  letI : Module ℂ U := Module.compHom U (φ : ℂ →+* Module.End ℝ U)
  have hsm : ∀ (z : ℂ) (v : U), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ U := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ U := Module.Finite.of_restrictScalars_finite ℝ ℂ U
  have hI : ∀ v : U, Complex.I • v = J v := fun v => by simp [hsm]
  let e := (Module.finBasis ℂ U).equivFun
  exact ⟨_, e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _⟩

theorem exists_ratForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v, (B u v : ℝ) = -om (p u) (p v) := by
  first
  | exact @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | (apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm ..)

theorem span_image {U : Type} [AddCommGroup U] [Module ℝ U]
    {V : Type} [AddCommGroup V] (p : V →+ U) (hsp : Submodule.span ℝ (Set.range p) = ⊤)
    (L : AddSubgroup V) (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) :
    Submodule.span ℝ (p '' (L : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨N, hN0, hx⟩ := hN x
  have h0 : (N : ℝ) ≠ 0 := by positivity
  have : p x = (N : ℝ)⁻¹ • p (N • x) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ h0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)

theorem fg_of_integral {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hom : ∀ x, om x = 0 → x = 0)
    {V : Type} [AddCommGroup V] (p : V →+ U) (hp : Function.Injective p) (L : AddSubgroup V)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    (AddSubgroup.toIntSubmodule L).FG := by
  have hfg : (Submodule.span ℝ (p '' (L : Set V))).FG := hsp ▸ Module.Finite.fg_top
  obtain ⟨s, hs, hss⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [hsp] at hss
  have h : ∀ (x : AddSubgroup.toIntSubmodule L) (y : s), ∃ k : ℤ, (k : ℝ) = om (p x) y := by
    rintro x ⟨y, hy⟩
    obtain ⟨y, hy', rfl⟩ := hs hy
    obtain ⟨k, hk⟩ := hint x x.2 y hy'
    exact ⟨k, hk.symm⟩
  choose k hk using h
  let φ : AddSubgroup.toIntSubmodule L →+ (s → ℤ) := AddMonoidHom.mk' k fun a b => by
    funext y
    apply Int.cast_injective (α := ℝ)
    simp [hk]
  have hφ : Function.Injective φ.toIntLinearMap := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext (hp ?_)
    rw [ZeroMemClass.coe_zero, map_zero]
    refine hom _ (LinearMap.ext_on hss.symm fun y hy => ?_)
    have : k x ⟨y, hy⟩ = 0 := congrFun hx ⟨y, hy⟩
    have h2 := hk x ⟨y, hy⟩
    rw [this] at h2
    simpa using h2.symm
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective _ hφ)

theorem not_linearIndependent : ∀ (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (J : U →ₗ[ℝ] U) (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ), (∀ x, J (J x) = -x) → (∀ x y, om x y = -om y x) → (∀ x y, om (J x) (J y) = om x y) → (∀ x, x ≠ 0 → om (J x) x < 0) → ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (p : V →+ U), Function.Injective p → Submodule.span ℝ (Set.range p) = ⊤ → ∀ L : AddSubgroup V, (∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) → (∀ x : V, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ f : Fin 2 → U → ℂ, (∀ k, Differentiable ℝ (f k)) → (∀ k w z, (fderiv ℝ (f k) w z - Real.pi * Complex.I * (om w z : ℂ) * f k w) + Complex.I * (fderiv ℝ (f k) w (J z) - Real.pi * Complex.I * (om w (J z) : ℂ) * f k w) = 0) → (∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = c v * Complex.exp (-(Real.pi * Complex.I) * (om z (p v) : ℂ)) * f k z) → ¬ LinearIndependent ℂ f := by
  intro U _ _ _ J om hJ halt hinv hpos V _ _ _ p hp hsp L hN hL c hc f hd hann hf hli
  obtain ⟨g, e, he⟩ := exists_coord J hJ
  have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  obtain ⟨Hm, hH, hHpos, hHim⟩ := GlobalTheory.PeriodNonempty.exists_herm
    (-(om.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap))
    (fun x y => by simp [halt (e.symm x)]) (fun x y => by simp [hs, hinv])
    (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
  have him : ∀ x y, (x ⬝ᵥ Hm.mulVec (star y)).im = -om (e.symm x) (e.symm y) := hHim
  have hpos' : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := hHpos
  have hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k := fun x hx => (hL x).1 hx
  obtain ⟨B, hB⟩ := exists_ratForm om p L hN hint
  have hspL := span_image p hsp L hN
  have hom : ∀ x, om x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [halt, hx] at this
    simp at this
  have hfg := fg_of_integral om hom p hp L hspL hint
  let P : V →ₗ[ℤ] (Fin g → ℂ) := (e.toLinearMap.toAddMonoidHom.comp p).toIntLinearMap
  have hP : ∀ v, P v = e (p v) := fun _ => rfl
  let E : (Fin g → ℂ) →L[ℝ] U := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hE : ∀ z, E z = e.symm z := fun _ => rfl
  have hconj : ∀ x y : Fin g → ℂ,
      x ⬝ᵥ Hm.mulVec (star y) = starRingEnd ℂ (y ⬝ᵥ Hm.mulVec (star x)) := fun x y => by
    change _ = star _
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  refine GlobalTheory.Dict.ThetaOne.proportional_of_selfDual B P (e.injective.comp hp)
    (AddSubgroup.toIntSubmodule L) hfg ?_ ?_ hH hpos' ?_ c hc
    (fun k w => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f k (e.symm w)) ?_ ?_ ?_
  · intro x
    refine (hL x).trans (forall₂_congr fun y _ => ⟨?_, ?_⟩)
    · rintro ⟨k, hk⟩
      refine ⟨-k, Rat.cast_injective (α := ℝ) ?_⟩
      rw [hB, hk]; simp
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      have := hB x y
      rw [hk] at this
      push_cast at this ⊢
      linarith
  · have : P '' (AddSubgroup.toIntSubmodule L : Set V) = e.toLinearMap '' (p '' (L : Set V)) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span, hspL, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [him, hB, hP, hP, e.symm_apply_apply, e.symm_apply_apply]
  · intro k
    refine GlobalTheory.T.differentiable_exp_mul_of_annihilated' g Hm hH (fun w => f k (E w)) ((hd k).comp E.differentiable) fun w z => ?_
    have h1 : fderiv ℝ (fun w => f k (E w)) w = (fderiv ℝ (f k) (E w)).comp E :=
      ((hd k (E w)).hasFDerivAt.comp w E.hasFDerivAt).fderiv
    have h2 := hann k (e.symm w) (e.symm z)
    rw [h1]
    simp only [ContinuousLinearMap.comp_apply, hE, him, hs]
    push_cast
    linear_combination h2
  · intro k v hv z
    have h1 : (om (e.symm z) (p v) : ℂ) = -((z ⬝ᵥ Hm.mulVec (star (P v))).im : ℂ) := by
      rw [him, hP, e.symm_apply_apply]; simp
    have h2 : e.symm (z + P v) = e.symm z + p v := by rw [map_add (f := _), hP, e.symm_apply_apply]
    have h3 : (Real.pi / 2 * ((z + P v) ⬝ᵥ Hm.mulVec (star (z + P v))) : ℂ) +
        -(Real.pi * Complex.I) * (om (e.symm z) (p v) : ℂ) =
        (Real.pi * (z ⬝ᵥ Hm.mulVec (star (P v))) +
          Real.pi / 2 * (P v ⬝ᵥ Hm.mulVec (star (P v)))) +
          Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)) := by
      rw [h1, star_add, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hconj (P v) z]
      have h4 := Complex.sub_conj (z ⬝ᵥ Hm.mulVec (star (P v)))
      push_cast at h4
      linear_combination (-(Real.pi : ℂ) / 2) * h4
    have h5 := congrArg Complex.exp h3
    rw [Complex.exp_add, Complex.exp_add _ (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)))] at h5
    simp only [h2, hf k v hv]
    linear_combination c v * f k (e.symm z) * h5
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    refine hli a (funext fun u => ?_)
    have h1 := congrFun ha (e u)
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      e.symm_apply_apply] at h1 ⊢
    refine mul_left_cancel₀
      (Complex.exp_ne_zero (Real.pi / 2 * (e u ⬝ᵥ Hm.mulVec (star (e u))))) ?_
    linear_combination h1

end GlobalTheory.VacuumLine
end
