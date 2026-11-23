module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Aesop.Main
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle068
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle001

@[expose] public section

section

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Br

private theorem cm_aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem cm_map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem cm_aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem cm_continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private noncomputable def eR (t : ℝ) : Ad ℚ := TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)

private theorem pInf_eR (t : ℝ) : TR.pInf ℚ (eR t) = algebraMap ℝ (TR.Rinf ℚ) t := (TR.infEq ℚ).symm_apply_apply _

private theorem pFin_eR (t : ℝ) : pFin ℚ (eR t) = 0 := rfl

private theorem pInf_sFin (a : Af ℚ) : TR.pInf ℚ (sFin ℚ a) = 0 := map_zero (TR.infEq ℚ).symm

private theorem pFin_sFin (a : Af ℚ) : pFin ℚ (sFin ℚ a) = a := rfl

private theorem pInf_rat (q : ℚ) : TR.pInf ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℝ (TR.Rinf ℚ) (q : ℝ) :=
  DFunLike.congr_fun (Subsingleton.elim ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))
    ((algebraMap ℝ (TR.Rinf ℚ)).comp (Rat.castHom ℝ))) q

private theorem pFin_rat (q : ℚ) : pFin ℚ (algebraMap ℚ (Ad ℚ) q) = algebraMap ℚ (Af ℚ) q := rfl

private theorem eR_add (s t : ℝ) : eR (s + t) = eR s + eR t := by simp only [eR, map_add (f := _)]

private theorem cm_upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (eR t) :=
  TR.ga_ext (by simp [upR, cm_map_aff, pInf_eR]) (by simp [upR, cm_map_aff, pFin_eR, cm_aff_zero])

private theorem cm_finGL_aff (a : Af ℚ) : finGL ℚ 2 (aff 1 a) = aff 1 (sFin ℚ a) :=
  TR.ga_ext (by simp [cm_map_aff, pInf_sFin, cm_aff_zero]) (by simp [cm_map_aff, pFin_sFin])

private theorem cm_decomp (x : Ad ℚ) (q : ℚ) :
    ∃ s : ℝ, x = algebraMap ℚ (Ad ℚ) q + eR s + sFin ℚ (pFin ℚ x - algebraMap ℚ (Af ℚ) q) := by
  refine ⟨ev (TR.pInf ℚ x) - q, TR.ad_ext ?_ ?_⟩
  · rw [map_add (f := _), map_add (f := _), pInf_rat, pInf_eR, pInf_sFin, add_zero, ← map_add (f := _), add_sub_cancel]
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    rfl
  · rw [map_add (f := _), map_add (f := _), pFin_rat, pFin_eR, pFin_sFin, add_zero, add_sub_cancel]

private theorem cm_mean {ψ : Ad ℚ → ℂ} {U : Set (Af ℚ)} (hU : IsOpen U) (h0 : 0 ∈ U) {N : ℕ} (hN : (N : Af ℚ) ∈ U)
    (hq : ∀ (q : ℚ) x, ψ (algebraMap ℚ (Ad ℚ) q + x) = ψ x) (hu : ∀ a ∈ U, ∀ x, ψ (x + sFin ℚ a) = ψ x) :
    Function.Periodic (fun t : ℝ => ψ (eR t)) N ∧ ∀ x, ∫ t in (0 : ℝ)..N, ψ (eR t + x) = ∫ t in (0 : ℝ)..N, ψ (eR t) := by
  have hp : Function.Periodic (fun t : ℝ => ψ (eR t)) N := fun t => by
    have e : eR (t + N) + sFin ℚ (N : Af ℚ) = algebraMap ℚ (Ad ℚ) (N : ℚ) + eR t := by
      refine TR.ad_ext ?_ ?_
      · rw [map_add (f := _), map_add (f := _), pInf_rat, pInf_eR, pInf_eR, pInf_sFin, add_zero, Rat.cast_natCast, map_add (f := _), add_comm]
      · rw [map_add (f := _), map_add (f := _), pFin_rat, pFin_eR, pFin_eR, pFin_sFin, zero_add, add_zero, map_natCast]
    beta_reduce
    rw [← hu _ hN, e, hq]
  refine ⟨hp, fun x => ?_⟩
  obtain ⟨q, hq'⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).exists_mem_open
    (hU.preimage (continuous_const.sub continuous_id : Continuous fun z : Af ℚ => pFin ℚ x - z)) ⟨pFin ℚ x, by simpa using h0⟩
  obtain ⟨s, hs⟩ := cm_decomp x q
  have e : ∀ t, ψ (eR t + x) = ψ (eR (t + s)) := fun t => by
    rw [hs, ← add_assoc, hu (pFin ℚ x - algebraMap ℚ (Af ℚ) q) hq', add_left_comm, hq, eR_add]
  simp only [e]
  rw [intervalIntegral.integral_comp_add_right (fun t => ψ (eR t)) s, zero_add, add_comm,
    hp.intervalIntegral_add_eq s 0, zero_add]

open GroundTheory.Automorphic.AutomorphicForm in
private theorem cm_fund : ∃ (_ : MeasurableSpace (BlockIx 2 1 → Ad ℚ)) (_ : BorelSpace (BlockIx 2 1 → Ad ℚ))
    (μ : Measure (BlockIx 2 1 → Ad ℚ)) (D : Set (BlockIx 2 1 → Ad ℚ)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratN ℚ 2 1) D μ := by
  have hμ : (unipMeasure ℚ 2 1).IsAddHaarMeasure := inferInstance
  have hB : BorelSpace (UPos 2 1 → AdeleRing (𝓞 ℚ) ℚ) := inferInstance
  have hL : ratN ℚ 2 1 = unipLattice ℚ 2 1 := AddSubgroup.ext fun x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
  exact ⟨_, hB, unipMeasure ℚ 2 1, unipFundamentalDomain ℚ 2 1, hμ, by
    rw [hL]; exact isAddFundamentalDomain_unipFundamentalDomain⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.cuspMean :
    UpperTheory.V.Br.CuspMean := by
  intro φ hφ g
  have hl := hφ.1.left
  have ho := hφ.1.level
  set u : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with hu
  have hc : Continuous fun x : Af ℚ => u⁻¹ * aff 1 x * u := (continuous_const.mul cm_continuous_aff).mul continuous_const
  have hU := ho.preimage hc
  have h0 : (0 : Af ℚ) ∈ (fun x : Af ℚ => u⁻¹ * aff 1 x * u) ⁻¹' {k | TR.finRep ℚ 2 k φ = φ} := by
    simp [cm_aff_zero]
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually (hU.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun y => ?_⟩
  set N : ℕ := n.factorial
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 n.factorial_pos
  have hq : ∀ (q : ℚ) x, φ.1 (aff 1 (algebraMap ℚ (Ad ℚ) q + x) * (g * upR y)) = φ.1 (aff 1 x * (g * upR y)) := fun q x => by
    rw [cm_aff_add, ← cm_map_aff, mul_assoc]
    exact hl _ _
  obtain ⟨hp, hm⟩ := cm_mean (ψ := fun x => φ.1 (aff 1 x * (g * upR y))) hU h0 hn hq fun a ha x => by
    have h1 : ∀ g, φ.1 (g * finGL ℚ 2 (u⁻¹ * aff 1 a * u)) = φ.1 g := fun g => congrFun (congrArg Subtype.val ha) g
    have e1 : g * upR y * finGL ℚ 2 (u⁻¹ * aff 1 a * u) = finGL ℚ 2 (aff 1 a) * (g * upR y) :=
      TR.ga_ext (by simp) (by simp [upR, ← hu, mul_assoc])
    rw [cm_aff_add, ← cm_finGL_aff, mul_assoc, ← e1, ← mul_assoc, h1]
  simp only [cm_upR_aff]
  refine ⟨hp, ?_⟩
  set c := ∫ t in (0 : ℝ)..N, φ.1 (aff 1 (eR t) * (g * upR y))
  obtain ⟨_, _, μ, D, hμ, hD⟩ := cm_fund
  obtain ⟨i1, i2, i3, i4, hco, hcu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * (g * upR y)) :=
    (smCont ℚ 2 φ ho).comp (hcu.mul continuous_const)
  have hinv : ∀ γ ∈ ratN ℚ 2 1, ∀ x, φ.1 (unip (γ + x) * (g * upR y)) = φ.1 (unip x * (g * upR y)) := by
    rintro _ ⟨q, rfl⟩ x
    rw [hx, hx]
    exact hq _ _
  obtain ⟨hfin, hP⟩ := UpperTheory.periodic_integral_fundamentalDomain_invariant _ (ratN ℚ 2 1) hco μ D hD
  have hint := (hP _ hinv).1 hψ
  have he : Continuous fun (t : ℝ) (_ : BlockIx 2 1) => eR t := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have key := avgZero _ (ratN ℚ 2 1) μ D hμ hD (fun x => φ.1 (unip x * (g * upR y)) - c / N) (hψ.sub continuous_const)
    (fun γ hγ x => by rw [hinv γ hγ]) _ he N hN fun x => by
      have h2 : Continuous fun t : ℝ => φ.1 (unip ((fun _ => eR t) + x) * (g * upR y)) := hψ.comp (he.add continuous_const)
      rw [intervalIntegral.integral_sub (h2.intervalIntegrable _ _) (by simp)]
      simp only [hx]
      rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, Complex.ofReal_natCast,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.2 n.factorial_pos.ne'), sub_eq_zero]
      exact hm _
  rw [integral_sub hint (integrableOn_const hfin), hφ.2 1 one_pos one_lt_two μ D hμ hD, setIntegral_const, zero_sub, neg_eq_zero,
    smul_eq_zero, div_eq_zero_iff] at key
  rcases key with key | key | key
  · exact absurd key (ENNReal.toReal_ne_zero.2 ⟨hD.measure_ne_zero (NeZero.ne μ), hfin⟩)
  · exact key
  · exact absurd key (Nat.cast_ne_zero.2 n.factorial_pos.ne')
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
open UpperHalfPlane hiding I

namespace UpperTheory.V.Br.DescentLift

private noncomputable def sc (t : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

private theorem sc_val (t : ℝ) : (sc t).val = !![Real.exp t, 0; 0, Real.exp t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sc]

private theorem sc_add (s t : ℝ) : sc (s + t) = sc s * sc t := by
  refine Units.ext ?_
  rw [Units.val_mul, sc_val, sc_val, sc_val]
  simp [Real.exp_add]

private theorem sc_zero : sc 0 = 1 := by
  refine Units.ext ?_
  rw [sc_val, Real.exp_zero, Units.val_one, Matrix.one_fin_two]

private theorem sc_inv (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) (g : GA ℚ 2) (t : ℝ) :
    φ.1 (g * upR (sc t)) = φ.1 g := by
  classical
  let X : TR.Lie ℚ 2 := TR.toL 1
  have hX : X = TR.toL (Matrix.single 0 0 (Pi.single Rat.infinitePlace 1)) +
      TR.toL (Matrix.single 1 1 (Pi.single Rat.infinitePlace 1)) := by
    ext i j u
    rw [Subsingleton.elim u Rat.infinitePlace]
    fin_cases i <;> fin_cases j <;> simp [X]
  have hL : TR.lie ℚ 2 X φ = 0 := by
    rw [hX, map_add (f := _), LinearMap.add_apply, ← h Rat.infinitePlace]
    simp only [TR.Eop]
    congr!
  let c : ℝ → GL (Fin 2) (TR.Rinf ℚ) := fun s => Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (sc s)
  have hcv : ∀ s i j v, (c s).val i j v = (sc s).val i j := fun _ _ _ _ => rfl
  have hc : HasDerivAt (fun s : ℝ => TR.toL (c s).val) X 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    have h1 : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    show HasDerivAt (fun s => (sc s).val i j) _ 0
    simp only [sc_val]
    fin_cases i <;> fin_cases j
    · simpa [X] using h1
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [X] using h1
  let f : ℝ → ℂ := fun t => φ.1 (g * upR (sc t))
  have hf : ∀ t, HasDerivAt f 0 t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * upR (sc t)) c X (by simp only [c, sc_zero, map_one]) hc
    rw [← TR.lie_apply, hL] at h1
    have h2 : HasDerivAt (fun s => f (t + s)) 0 0 := by
      simpa only [f, sc_add, map_mul, mul_assoc] using! h1
    have h3 := HasDerivAt.comp_sub_const t t (f := fun s => f (t + s)) (by rw [sub_self]; exact h2)
    simpa using h3
  have h4 := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt) (fun t => (hf t).deriv) t 0
  simpa only [f, sc_zero, map_one, mul_one] using h4

private noncomputable def rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    rw [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

private theorem rot_val (θ : ℝ) : (rot θ).val = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem rot_det (θ : ℝ) : (rot θ).val.det = 1 := by
  rw [rot_val, Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem rot_eig (φ : TR.Sm ℚ 2) (z : ℂ) (h : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ) (g : GA ℚ 2) (θ : ℝ) :
    φ.1 (g * upR (rot θ)) = Complex.exp (z * θ) * φ.1 g := by
  have := rotEig ℚ φ z h (fun _ => θ) (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (rot θ)) (by
    ext i j v
    fin_cases i <;> fin_cases j <;> rfl) g
  simpa using! this

private theorem nsl_rot (k : ℕ) (f : ℍ → ℂ) (θ : ℝ) :
    nsl k f (rot θ).val UpperHalfPlane.I = Complex.exp (Complex.I * k * θ) * f UpperHalfPlane.I := by
  have e : (((rot θ).val 1 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 1 1 : ℝ) = Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    ring
  have e' : (((rot θ).val 0 0 : ℝ) : ℂ) * (UpperHalfPlane.I : ℍ) + ((rot θ).val 0 1 : ℝ) =
      Complex.I * Complex.exp (-(θ * Complex.I)) := by
    rw [← neg_mul, Complex.exp_mul_I]
    simp [rot_val]
    linear_combination (Complex.sin θ) * Complex.I_mul_I
  simp only [nsl]
  rw [e, e', rot_det, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _), ← Complex.exp_int_mul]
  have : ofComplex Complex.I = UpperHalfPlane.I := ofComplex_apply UpperHalfPlane.I
  simp only [abs_one, Real.one_rpow, sign_one, SignType.coe_one, Complex.ofReal_one, one_mul, this]
  congr 2
  push_cast
  ring

private theorem nsl_aff (k : ℕ) (φ : GA ℚ 2 → ℂ) (y x : ℝ) (hy : 0 < y) :
    nsl k (down k φ) (aff (Units.mk0 y hy.ne') x).val UpperHalfPlane.I = φ (upR (aff (Units.mk0 y hy.ne') x)) := by
  have hv : (aff (Units.mk0 y hy.ne') x).val = !![y, x; 0, 1] := rfl
  have hd : (!![y, x; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = y := by simp
  let z : ℍ := ⟨⟨x, y⟩, hy⟩
  have hz : down k φ z = ((y ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ (upR (aff (Units.mk0 y hy.ne') x)) := rfl
  have e : (y : ℂ) * Complex.I + x = (z : ℂ) := by
    apply Complex.ext <;> simp [z]
  simp only [nsl]
  rw [hv, hd, abs_of_pos hy, sign_pos hy]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, Complex.ofReal_one, zero_mul, zero_add, one_zpow, mul_one, div_one, SignType.coe_one, one_mul, coe_I]
  rw [e, ofComplex_apply, hz, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hy]
  simp

private theorem iwasawa (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    ∃ (y : ℝ) (hy : 0 < y) (x θ t : ℝ), h = aff (Units.mk0 y hy.ne') x * rot θ * sc t := by
  set a := h.val 0 0 with ha
  set b := h.val 0 1 with hb
  set c := h.val 1 0 with hc
  set d := h.val 1 1 with hd
  rw [Matrix.det_fin_two, ← ha, ← hb, ← hc, ← hd] at hh
  let w : ℂ := ⟨d, -c⟩
  have hw : w ≠ 0 := by
    intro h0
    have h1 : d = 0 := congrArg Complex.re h0
    have h2 : -c = 0 := congrArg Complex.im h0
    rw [h1, neg_eq_zero.1 h2] at hh
    simp at hh
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : ‖w‖ * Real.cos w.arg = d := Complex.norm_mul_cos_arg w
  have h2 : ‖w‖ * Real.sin w.arg = -c := Complex.norm_mul_sin_arg w
  have h3 : ‖w‖ ^ 2 = c ^ 2 + d ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [w]; ring
  have hn : 0 < c ^ 2 + d ^ 2 := h3 ▸ pow_pos hr 2
  refine ⟨(a * d - b * c) / (c ^ 2 + d ^ 2), div_pos hh hn, (a * c + b * d) / (c ^ 2 + d ^ 2), w.arg, Real.log ‖w‖, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, sc_val, rot_val, Real.exp_log hr]
  change _ = !![(a * d - b * c) / (c ^ 2 + d ^ 2), (a * c + b * d) / (c ^ 2 + d ^ 2); 0, 1] * _ * _
  rw [Matrix.eta_fin_two h.val, ← ha, ← hb, ← hc, ← hd, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  refine congrArg₂ (fun p q => ![p, q]) (congrArg₂ (fun p q => ![p, q]) ?_ ?_) (congrArg₂ (fun p q => ![p, q]) ?_ ?_)
  · field_simp
    linear_combination (-(a * d - b * c)) * h1 + (a * c + b * d) * h2
  · field_simp
    linear_combination (-(a * d - b * c)) * h2 - (a * c + b * d) * h1
  · linear_combination h2
  · linear_combination -h1

private theorem pos_case (k : ℕ) (φ : TR.Sm ℚ 2) (hφ : IsLow k φ) (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    φ.1 (upR h) = nsl k (down k φ.1) h.val UpperHalfPlane.I := by
  obtain ⟨y, hy, x, θ, t, rfl⟩ := iwasawa h hh
  have e : (aff (Units.mk0 y hy.ne') x * rot θ * sc t).val = Real.exp t • ((aff (Units.mk0 y hy.ne') x).val * (rot θ).val) := by
    rw [Units.val_mul, Units.val_mul, sc_val]
    ext i j
    fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  rw [e, (nslMul k _).2.2.1 _ _ (Real.exp_pos t),
    ← (nslMul k _).1 _ _ (Matrix.isUnits_det_units _).ne_zero (by rw [rot_det]; exact one_pos), nsl_rot, nsl_aff k _ y x hy,
    map_mul, map_mul, sc_inv φ hφ.one, rot_eig φ _ hφ.wt]

private def epsQ : GL (Fin 2) ℚ := ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private theorem toR_epsQ : (toR epsQ).val = eps := by
  ext i j
  show Rat.castHom ℝ (epsQ.val i j) = _
  fin_cases i <;> fin_cases j <;> simp [epsQ, eps]

private theorem toF_epsQ (N : ℕ) : toF epsQ ∈ K1G N := by
  have h : ∀ a b, (toF epsQ).val a b ∈ Ohat ℚ := fun a b => by
    show algebraMap ℚ (Af ℚ) (epsQ.val a b) ∈ _
    fin_cases a <;> fin_cases b <;> simp [epsQ, one_mem, zero_mem]
  refine (memK N _).2 ⟨h, ?_, ⟨0, zero_mem _, ?_⟩, 0, zero_mem _, ?_⟩
  · rw [← map_inv]
    exact h
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 0) = _
    simp [epsQ]
  · show algebraMap ℚ (Af ℚ) (epsQ.val 1 1) - 1 = _
    simp [epsQ]

end UpperTheory.V.Br.DescentLift

open UpperTheory.V.Br.DescentLift in
theorem UpperTheory.V.Br.downLift :
    UpperTheory.V.Br.DownLift := by
  intro k N _ φ hr hφ hK γ h u hu
  have hfin : ∀ u ∈ K1G N, ∀ g, φ.1 (g * finGL ℚ 2 u) = φ.1 g := fun u hu g =>
    congrFun (congrArg Subtype.val (hK u hu)) g
  rw [hr, hfin u hu]
  rcases lt_or_gt_of_ne (Matrix.isUnits_det_units h).ne_zero with hd | hd
  · have e : (toR epsQ * h).val = eps * h.val := by rw [Units.val_mul, toR_epsQ]
    have hd' : 0 < (toR epsQ * h).val.det := by
      rw [e, Matrix.det_mul]
      simpa [eps, Matrix.det_fin_two_of] using hd
    rw [← (nslMul k _).2.1, ← e, ← pos_case k φ hφ _ hd', ← hr epsQ (upR h), ratGL_eq, mul_assoc, ← upR_comm, ← mul_assoc,
      hfin _ (toF_epsQ N), map_mul]
  · exact pos_case k φ hφ h hd
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

private theorem untwist (k N : ℕ) [NeZero N] (hk : 1 ≤ k) (χ ψ : DirichletCharacter ℂ N) (g : Eigenform k N χ) :
    ∃ (χ' : DirichletCharacter ℂ (N * N)) (g' : Eigenform k (N * N) χ'), ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      g'.a p * ψ (p : ZMod N) = g.a p ∧ χ' (p : ZMod (N * N)) * ψ (p : ZMod N) ^ 2 = χ (p : ZMod N) := by
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  obtain ⟨h, hc, hn⟩ := clTwist N k χ ψ⁻¹ g.f g.char
  have h0 : h ≠ 0 := by
    rintro rfl
    have := hn 1
    rw [g.one, Nat.cast_one, map_one, mul_one] at this
    simp [coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨g', hg'⟩ := eigEx (N * N) k hk _ h hc h0 fun p => ψ⁻¹ (p : ZMod N) * g.a p
  refine ⟨_, g', fun p hp hd => ?_⟩
  have hu : IsUnit (p : ZMod (N * N)) :=
    (ZMod.isUnit_prime_iff_not_dvd hp).2 fun e => hd ((hp.dvd_mul.1 e).elim id id)
  have hu' : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ⁻¹ ^ 2) (p : ZMod (N * N)) =
      χ (p : ZMod N) * ψ⁻¹ (p : ZMod N) ^ 2 := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ⁻¹ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_natCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  have e1 : ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hu']
  constructor
  · rw [hg' p hp fun n h1 => ?_]
    · linear_combination g.a p * e1
    have := g.eig p hp n h1
    rw [e, hn, hn n, Nat.cast_mul, map_mul, Eigenform.a]
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp.pos] at this ⊢
      rw [hn, Nat.cast_mul, map_mul]
      linear_combination ψ⁻¹ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ⁻¹ (m : ZMod N)) * this
    · rw [if_neg hpn] at this ⊢
      linear_combination ψ⁻¹ (p : ZMod N) * ψ⁻¹ (n : ZMod N) * this
  · rw [e]
    linear_combination χ (p : ZMod N) * (ψ⁻¹ (p : ZMod N) * ψ (p : ZMod N) + 1) * e1

private theorem eig_unique {k N p : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} (hf : f ≠ 0)
    {a b : ℂ} (ha : IsEigAt k χ f p a) (hb : IsEigAt k χ f p b) : a = b := by
  by_contra h
  exact hf ((finDim N k).2 f fun n hn =>
    (mul_eq_zero.1 (show (a - b) * coef f n = 0 by linear_combination hb n hn - ha n hn)).resolve_left (sub_ne_zero.2 h))

private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem lie_one (φ : TR.Sm ℚ 2) (h : ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) : TR.lie ℚ 2 (TR.oneL ℚ 2) φ = 0 := by
  classical
  have hX : TR.lie ℚ 2 (TR.oneL ℚ 2) = ∑ i, TR.lieS ℚ 2 i i 1 := by

    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin 2) (α := TR.Rinf ℚ)).symm
  have h1 : ∀ i, TR.lieS ℚ 2 i i 1 = TR.Eop Rat.infinitePlace i i := fun i => by
    rw [TR.Eop_eq]
    congr 1
    funext v
    rw [Subsingleton.elim v Rat.infinitePlace]
    simp
  rw [hX, Fin.sum_univ_two, h1, h1]
  exact h _

private theorem ev_not_dvd {a : ℕ} (h : a ≠ 0) : ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
end
