module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecTheta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem isThetaFunO_of_thetaAt (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {e : AE D} {Λ : AddSubgroup (WO S T)}
    {c : ℂ} {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) : IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
  {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}

theorem isThetaFunO_stepVec {LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank}
    {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

theorem isThetaFunO_thPVec {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

end GlobalTheory.VecTheta

end
end

section

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.SmoothLowKStable

open Formalism.MainNotions.S GlobalTheory.GardingVec

theorem list_prod_conj {n : ℕ} {g h : Matrix (Fin n) (Fin n) ℂ} (hgh : g * h = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : l.prod * g = g * (l.map fun x => h * x * g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc, ih]
    simp only [← Matrix.mul_assoc, hgh, Matrix.one_mul]

theorem smoothVec_apply {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hmul : ∀ g ∈ UJset ε, ∀ h ∈ UJset ε, σ (g * h) = σ g * σ h) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ UJset ε) {v : H}
    (hv : Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ k v) := by
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have hk' : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  set g := P⁻¹ * k * P with hg
  have hPg : P * g = k * P := by rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * P := by rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hk', h]
  have hgu : IsUnit g := by
    have : IsUnit (gᴴ * G * g).det := by rw [hgG]; exact (Matrix.isUnit_iff_isUnit_det G).1 hG
    rw [Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_of_mul_isUnit_right this)
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgd
  have hGg : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hGg' : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← hgG]
    rw [Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc, ← conjTranspose_mul, hgg, conjTranspose_one, Matrix.one_mul]
  intro m Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [hGg, hGg']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hv m (fun i => g⁻¹ * Xs i * g) hY
  have hmem : ∀ (Ys : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (Ys i)ᴴ * G + G * Ys i = 0) → ∀ t : Fin m → ℝ,
      P * (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod * P⁻¹ ∈ UJset ε := fun Ys hYs t => by
    refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_mem hG (hYs i) _
  have key : ∀ t : Fin m → ℝ,
      σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) (σ k v)
        = σ k (σ (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) v) := fun t => by
    have e1 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g)))
        = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun x => g⁻¹ * x * g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hgu, Matrix.mul_smul, Matrix.smul_mul]
    have e2 := list_prod_conj hgg (List.ofFn fun i => NormedSpace.exp (t i • Xs i))
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← hmul _ (hmem Xs hX t) _ hk,
      ← hmul _ hk _ (hmem _ hY t), e1]
    congr 2
    have e3 : P⁻¹ * k = g * P⁻¹ := by rw [hg, Matrix.mul_assoc _ P, hPP, Matrix.mul_one]
    rw [Matrix.mul_assoc _ P⁻¹, e3, ← Matrix.mul_assoc, Matrix.mul_assoc P, e2]
    simp only [← Matrix.mul_assoc, hPg]
  have := ((σ k).restrictScalars ℝ).contDiff.comp hs
  refine (funext key : _ = _) ▸ this

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isKStableOn_lowKSub_inf_sm (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (τ : D.what₂.Tau) : IsKStableOn (M.ε τ) (M.σ τ) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ⊓ M.sm τ) := by
  intro k hk w hw
  have hkU : k ∈ UJset (M.ε τ) := by
    show kᴴ * Formalism.REAL.Jm _ * k = Formalism.REAL.Jm _
    have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · have : lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
        ≤ (lowKSub (M.ε τ) (M.lam τ) (M.σ τ)).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      sSup_le fun T hT v hv => (le_sSup hT : T ≤ _) (hT.2.1 k hk v hv)
    exact this hw.1
  · have : M.sm τ ≤ (M.sm τ).comap (M.σ τ k : _ →ₗ[ℂ] _) :=
      Submodule.span_le.2 fun v hv => Submodule.subset_span
        (smoothVec_apply (M.ds τ).2.2.1.1.2 (M.fr_unit τ) (M.fr_gram τ) hkU hv)
    exact this hw.2

end GlobalTheory.SmoothLowKStable

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompactModel

theorem mem_Kset_of_mem_UJset {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g ∈ Formalism.REAL.Kset (allPos k) := by
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    simp [Formalism.REAL.Jm, allPos]
  have h : gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) := hg
  rw [hJ, Matrix.mul_one] at h
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 h, ?_⟩
  rw [hJ, Matrix.mul_one, Matrix.one_mul]

theorem list_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : (l.map fun x => g⁻¹ * x * g).prod = g⁻¹ * l.prod * g := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp [Matrix.nonsing_inv_mul _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem smoothVec_stable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ UJset ε) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) (σ u w) := by
  obtain ⟨⟨h1, hmul⟩, -, -⟩ := hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hJ : IsUnit (Formalism.REAL.Jm ε) := IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul hJ).mul hP
  have hu' : uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε := hu
  have huu : IsUnit u := by
    have : IsUnit (uᴴ * Formalism.REAL.Jm ε * u) := by rw [hu']; exact hJ
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det u).2 (isUnit_of_mul_isUnit_right this)
  set g : Matrix (Fin n) (Fin n) ℂ := P⁻¹ * u * P with hgdef
  have hPi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hP
  have hg : IsUnit g := (hPi.mul huu).mul hP
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hPg : P * g = u * P := by
    rw [hgdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hug : u = P * g * P⁻¹ := by
    rw [hPg, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hgG : gᴴ * G * g = G := by
    calc gᴴ * G * g = (P * g)ᴴ * Formalism.REAL.Jm ε * (P * g) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * (uᴴ * Formalism.REAL.Jm ε * u) * P := by
          rw [hPg]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hu', h]
  clear_value g
  intro k Xs hX
  have hY : ∀ i, (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g) = 0 := by
    intro i
    have hXi : (Xs i)ᴴ * G + G * Xs i = 0 := hX i
    have e1 : G * g⁻¹ = gᴴ * G := by
      conv_lhs => rw [← hgG]
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hgd]
    have e2 : (g⁻¹)ᴴ * G = G * g := by
      conv_lhs => rw [← hgG]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hgd]
      simp
    calc (g⁻¹ * Xs i * g)ᴴ * G + G * (g⁻¹ * Xs i * g)
        = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * Xs i * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * G + G * Xs i) * g := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hXi]; simp
  have hs := hw k (fun i => g⁻¹ * Xs i * g) hY
  have hs2 := ((σ u).restrictScalars ℝ).contDiff.comp hs
  convert hs2 using 1
  funext t
  have hmem : ∀ Zs : Fin k → Matrix (Fin n) (Fin n) ℂ, (∀ i, (Zs i)ᴴ * G + G * Zs i = 0) →
      P * (List.ofFn fun i => NormedSpace.exp (t i • Zs i)).prod * P⁻¹ ∈ UJset ε := fun Zs hZ => by
    refine GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun a ha => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact GlobalTheory.GardingVec.exp_mem hG (hZ i) _
  have e3 : (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = g⁻¹ * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← list_prod_conj hg, List.map_ofFn]
    congr 2
    funext i
    rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hg]
    simp
  have a := hmul _ (hmem Xs hX) _ hu
  have b := hmul _ hu _ (hmem _ hY)
  have e4 : P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ * u
      = u * (P * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod * P⁻¹) := by
    rw [e3, hug]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.mul_nonsing_inv_cancel_left _ _ hgd]
  rw [e4, b] at a
  exact (congrArg (fun f => f w) a).symm

theorem model_allPos : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau),
    M.ε τ = allPos V.rank → FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧
      IsURepOn (UJset (allPos V.rank)) (M.σ τ) ∧
      IsKTypeOf (allPos V.rank) (M.σ τ) (Formalism.QuantumDeterminants.lowK (allPos V.rank) (M.lam τ)) ⊤ := by
  intro D V S M τ hε
  obtain ⟨-, -, hrep, hirr, -, ⟨T, hT⟩, -⟩ := M.ds τ
  have hT' := hT
  rw [hε] at hT'
  have hTtop : T = ⊤ := by
    obtain ⟨hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩ := hT'
    refine (hirr T T.closed_of_finiteDimensional fun g hg => hst g ?_).resolve_left ?_
    · rw [hε] at hg
      exact mem_Kset_of_mem_UJset hg
    · exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  subst hTtop
  have hfd : FiniteDimensional ℂ (M.H τ) := by
    have := hT'.1
    exact Module.Finite.equiv Submodule.topEquiv
  refine ⟨hfd, ?_, hε ▸ hrep, hT'⟩
  refine (hirr (M.sm τ) (M.sm τ).closed_of_finiteDimensional fun u hu v hv => ?_).resolve_left
    (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  have hle : (M.sm τ).map (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ) ≤ M.sm τ := by
    refine (Submodule.map_span_le _ _ _).2 fun w hw => Submodule.subset_span ?_
    exact smoothVec_stable hrep (M.fr_unit τ) (M.fr_gram τ) hu hw
  exact hle ⟨v, hv, rfl⟩

end GlobalTheory.CompactModel
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | exact GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | (intros; apply GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SplitTower

theorem splits_completely_of_intermediate :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : ℕ), p.Prime →
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 L)).ncard = Module.finrank ℚ L →
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
  intro K L _ _ _ _ _ p hp hcount 𝔭 hp𝔭
  rw [GlobalTheory.Bauer.ncard_eq_finrank_iff K L 𝔭]
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  have hPmax : P.IsMaximal := by
    exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI := hPmax
  haveI : Fintype (P.primesOver (𝓞 L)) := (IsDedekindDomain.primesOver_finite P (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 L)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have h1 : (P.primesOver (𝓞 L)).ncard = ∑ _q : P.primesOver (𝓞 L), 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hall : ∀ Q ∈ P.primesOver (𝓞 L), Q.ramificationIdx ℤ * Q.inertiaDeg ℤ = 1 := by
    rw [← hsum, h1, Finset.sum_eq_sum_iff_of_le] at hcount
    · intro Q hQ
      exact (hcount ⟨Q, hQ⟩ (Finset.mem_univ _)).symm
    · rintro ⟨Q, hQ, _⟩ -
      exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := _) Q) (Ideal.inertiaDeg_pos Q _)
  intro Q hQ
  obtain ⟨hQp, hQ𝔭⟩ := hQ
  haveI := 𝔭.isPrime
  haveI h𝔭P : 𝔭.asIdeal.LiesOver P := by
    refine ⟨hPmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_⟩
    rw [hPdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hp𝔭
  haveI : Q.LiesOver P := Ideal.LiesOver.trans Q 𝔭.asIdeal P
  have h := hall Q ⟨hQp, inferInstance⟩
  rw [Ideal.ramificationIdx_tower 𝔭.asIdeal Q, Ideal.inertiaDeg_tower 𝔭.asIdeal Q] at h
  refine Nat.eq_one_of_dvd_one ?_
  rw [← h]
  exact ⟨𝔭.asIdeal.ramificationIdx ℤ * 𝔭.asIdeal.inertiaDeg ℤ, by ring⟩

end GlobalTheory.SplitTower
end
