module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.SpLieD

open Matrix GlobalTheory.RealLift.SpLie

theorem exists_sp_rightActD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      letI : NormedRing (Mat (R w) (S w)) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Mat (R w) (S w)) := Matrix.linftyOpNormedAlgebra
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    simp only [Function.comp_apply]
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.HoweD.SpLieD
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ColActionD

theorem exists_symplectic_hom_of_unitary_dep : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [GlobalTheory.ColAction.signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    GlobalTheory.ColAction.mem_symplecticGroup_of_sympl _
      (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColActionD
end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_lie_wts_comm : ∀ P Q R S : ℕ, IsLieAct (fockAct1 P Q R S) ∧ IsLieAct (fockAct2 P Q R S) ∧
    (∀ v, v ∈ ⨆ μ : Ix P Q → ℚ, wtSub (fockAct1 P Q R S) μ) ∧ (∀ v, v ∈ ⨆ μ : Ix R S → ℚ, wtSub (fockAct2 P Q R S) μ) ∧
    ∀ X Y f, fockAct1 P Q R S X (fockAct2 P Q R S Y f) = fockAct2 P Q R S Y (fockAct1 P Q R S X f) := by
  intro P Q R S
  obtain ⟨h1, h2, hc⟩ := GlobalTheory.FockPair.pair_lie_commute P Q R S
  obtain ⟨w1, w2⟩ := GlobalTheory.FockPolGK.pol_locFin_weights P Q R S
  refine ⟨h1, h2, fun v => (w1 v).2, fun v => (w2 v).2, fun X Y f => ?_⟩
  have := LinearMap.congr_fun (hc X Y) f
  simpa only [Module.End.mul_apply] using this

end GlobalTheory.HoweR
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem exists_isHW_of_fd : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act →
    (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∀ U : Submodule ℂ V, U ≠ ⊥ →
    FiniteDimensional ℂ U → KStable act U → ∃ (μ : Ix p q → ℚ) (v : V), v ∈ U ∧ IsHW act μ v := by
  intro p q V _ _ act hL hd U hU hfd hK
  exact GlobalTheory.BlockReps.exists_hw (fun Y Z _ _ => hL Y Z) hK (fun v _ => hd v) hU

end GlobalTheory.HoweR
end

section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π ℓ → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, HasDerivAt (fun t : ℝ => ℓ (π (NormedSpace.exp (t • X)) v)) (ℓ (dRep π X v)) 0 := by
  first | exact @GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | exact GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit | (intros; apply GlobalTheory.SobOrbit.hasDerivAt_sobCont_orbit <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | exact GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure | (intros; apply GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatReflection

theorem latHat_eq_lamHat {D : D7} (V : HSp D) : Formalism.L2.Pj.latHat V = Formalism.L2.NTheta.LamHat V := by
  rw [GlobalTheory.LatDual.lamHat_eq_hat]
  exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1

end GlobalTheory.LatReflection
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open Formalism.IndefR.Rat Formalism.IndefR.Cx.CxData in
theorem ratMuP_of_rowTest : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PrincipalLevelBijective F → (R.toCx3 F).RATmu (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F hT hH2
  obtain ⟨N, ψ, hψ, hr⟩ := hT
  obtain ⟨hinj0, hall⟩ := hH2
  intro t i k
  have hmem : (R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1) ∈
      LinearMap.range ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) := by
    rw [← (hall t).2]; exact LinearMap.mem_range_self _ _
  have key := coord_rat _ ψ hψ ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0) hinj0
    (fun j l => by rw [CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _)
    (solve ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false A3.A.fam.μ0)
      ((R.toCx3 F).iC (crdOf3 A3 ⊥ 1 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false t (Pi.single k 1)))
    (fun j => by rw [solve_spec _ _ hmem, CxData.iC, Formalism.IndefR.Rat.lin_single]; exact hr _ _ _) i
  obtain ⟨a, ha⟩ := key
  exact ⟨a, ha⟩

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.AdjPart

theorem adjoint_injective_on_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks), (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R hP hB p w hw h0
  have h2 := hB A3.A.μ0 p w hw
  rw [LinearMap.comp_apply, h0, map_zero, Formalism.IndefR.Links.RealDat3.prod_lamN] at h2
  have hpos : 0 < R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 :=
    mul_pos hP.1 (Finset.prod_pos fun j _ => hP.2 j A3.A.μ0 p)
  have hne : ((R.kap * ∏ j : Fin D.R.m, R.lam3 j A3.A.μ0 p A3.A.v0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  exact (smul_eq_zero.1 h2.symm).resolve_left hne

end GlobalTheory.AdjPart
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.GEqBr



theorem geq_br : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.phase → R.PGEquiv F → (∀ t g (v : (A3.A.MtildeCSD t).Forms), R.Th t (R.jX t (A3.A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧ ∀ i t g (v : (A3.A.MtCSD i t).Forms), R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A3.A) g (R.thG i t (R.jV i t v)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hph hG
  refine ⟨fun t g v => hG.1 t g v, fun i t g v => ?_⟩
  have h : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) =
      R.gW i (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t v)) := hG.2 i t g v
  rw [map_smul] at h
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hph i).1, norm_zero] at this
    exact one_ne_zero this
  exact smul_right_injective _ hne h

end GlobalTheory.GEqBr
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.PrincipalRows

theorem theta_adjoint_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    (cv : CrdV A) (hKR : X.KFormR) (hJR : X.JIsoR cv) (hRT : Formalism.IndefR.Rat.RowTest X) (t : Bs.Tup) (S : Submodule ℂ X.EE)
    (hZ : ∀ z ∈ X.Z t, X.Θ t (X.jR t z) ∈ S) (e : X.EE) : X.Θ t (LinearMap.adjoint (X.Θ t) e) ∈ S := by
  obtain ⟨N, ψ, hψ, hr⟩ := hRT
  have hspan : Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t)) :=
    Formalism.IndefR.Rat.range_adjoint_rat Bs.v0.embedding (X.jR t) (cv.hR t) (CxData.bR t) (hKR t).1 (hKR t).2 (hJR t) (X.Θ t) ψ hψ
      (fun i x => hr t i x)
  have hsub : LinearMap.range (LinearMap.adjoint (X.Θ t)) ≤ S.comap (X.Θ t) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact hZ z hz
  exact hsub ⟨e, rfl⟩

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows

theorem mem_range_toF_full {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (Z : Submodule K B.S.Forms) (z : B.S.Forms) (hz : z ∈ Z)
    (hg : z ∈ B.goodF Xc) : z ∈ LinearMap.range (B.toF ⟨Xc, ⊥, 1⟩ Z) := by
  rw [GlobalTheory.OneForm.range_toF]
  refine ⟨hz, ?_⟩
  obtain ⟨w, hw⟩ := hg
  refine ⟨w, ?_⟩
  rw [← hw, Formalism.L2.DIV.CSD.gaOp, GlobalTheory.OneForm.asAlg_eq_sum, LinearMap.sum_apply]
  rfl

theorem theta_base_forms_mem_principal_good_part {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type}
    {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3) {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
    {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} (hIB : X.zs.InBlock) :
    ∀ z ∈ X.Z A3.A.fam.μ0, X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 z) ∈
      EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) := by
  intro z hz
  have h1 : z ∈ (A3.A.fam.R A3.A.fam.μ0).ZHg A3.A.fam.X := hIB.1 A3.A.fam.μ0 hz
  obtain ⟨x, hx⟩ := mem_range_toF_full (A3.A.fam.R A3.A.fam.μ0) A3.A.fam.X (X.zs.Z A3.A.fam.μ0) z hz h1.2
  refine ⟨cpt A3.A.v0.embedding x, ?_⟩
  have h3 := GlobalTheory.OneForm.iC_cpt X (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0 x
  refine h3.trans ?_
  exact congrArg (fun y => X.Θ A3.A.fam.μ0 (X.jR A3.A.fam.μ0 y)) hx

end GlobalTheory.PrincipalRows

namespace GlobalTheory.PrincipalRows



theorem principal_level_rows_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → (⨆ p, R.EEp3 p) = ⊤ → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (R.toCx3 F).zs.InBlock → EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC hTop hPos hB hRT hIB
  have hKR : (R.toCx3 F).KFormR := RealDat3.kFormR_of hC.base.models
  have hJR : (R.toCx3 F).JIsoR F.cv := RealDat3.jIsoR_of hC.base.models
  have hmem := theta_adjoint_mem (R.toCx3 F) F.cv hKR hJR hRT A3.A.fam.μ0
    (EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc))
    (theta_base_forms_mem_principal_good_part A3 (R.toCx3 F) hIB)

  have hpart : ∀ p, ∀ y ∈ R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro p y hy
    have hc : (0 : ℝ) < R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p := by
      refine mul_pos hPos.1 (Finset.prod_pos fun j _ => ?_)
      unfold RealDat3.lamN
      split_ifs
      · exact hPos.2 _ _ _
      · exact one_pos
    have hne : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hce : ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y ∈ R.EEp3 p :=
      (R.EEp3 p).smul_mem _ hy
    have key : R.Th A3.A.fam.μ0 (LinearMap.adjoint (R.Th A3.A.fam.μ0)
        (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y)) = y := by
      refine (hB A3.A.fam.μ0 p _ hce).trans ?_
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 := hmem (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))
    have h4 : (R.toCx3 F).Θ A3.A.fam.μ0 (LinearMap.adjoint ((R.toCx3 F).Θ A3.A.fam.μ0)
        (Tw.mk (twAt D.what₂.embLL A3.A.v0) (((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN A3.A.fam.μ0 j p : ℝ) : ℂ)⁻¹ • y))) = Tw.mk (twAt D.what₂.embLL A3.A.v0) y := by
      show Tw.map _ (R.Th A3.A.fam.μ0) (LinearMap.adjoint (Tw.map _ (R.Th A3.A.fam.μ0)) _) = _
      rw [Tw.adjoint_map]
      exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) key
    rw [h4] at h3
    exact h3
  rw [eq_top_iff]
  intro e0 _
  have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) e0 ∈ ⨆ p, R.EEp3 p := by rw [hTop]; exact Submodule.mem_top
  have hall : ∀ y ∈ ⨆ p, R.EEp3 p, (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) := by
    intro y hy
    exact Submodule.iSup_induction R.EEp3 (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈
      EEg3 A3 (R.toCx3 F) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) hy hpart
      (Submodule.zero_mem _) (fun a b ha hb => Submodule.add_mem _ ha hb)
  exact hall _ hx

end GlobalTheory.PrincipalRows
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tieIn_of_nonempty_tie :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ⟨fw⟩ => ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

end GlobalTheory
end
