module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lin_addChar_sum {A : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) {ι : Type} (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

theorem lin_holValueAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (h : ι → ℂ → ℂ) (v : ι → ℂ) (s₀ : ℂ)
    (hh : ∀ i ∈ s, HolValueAt (h i) s₀ (v i)) :
    HolValueAt (fun z => ∑ i ∈ s, c i * h i z) s₀ (∑ i ∈ s, c i * v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((holValueAt_const (c j) s₀).mul (hh j (Finset.mem_insert_self j s))).add
      (ih fun i hi => hh i (Finset.mem_insert_of_mem hi))

section SDl

variable (d : SD σ)

def linRhoL (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem lin_T_eq (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T Φ X = d.l (linRhoL d X Φ) := rfl

theorem lin_T_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : Mx F E d.m d.n) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by

  simp only [lin_T_eq, map_sum, map_smul, smul_eq_mul]

theorem section_linear_finset_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (x : d.G) :
    d.sec0 (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.sec0 (Φs i) x := by

  simp only [SD.sec0, map_sum, map_smul, smul_eq_mul]

theorem lin_om_mem (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ h

theorem lin_S_mem (g : UA σ d.A.J) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch := d.ok.dbl.lin.pres g Φ h

theorem lin_sum_mem {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    ∑ i ∈ s, c i • Φs i ∈ d.sch :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (h i hi)

theorem lin_thetaSum_sum (hT : TTheta) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    thetaSum F (∑ i ∈ s, c i • Φs i) = ∑ i ∈ s, c i * thetaSum F (Φs i) := by
  have h1 := (hT F E σ d _ (lin_sum_mem d s c Φs h)).1
  have h2 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => ∑ i ∈ s, c i * d.T (Φs i) (incM F X))
      (∑ i ∈ s, c i * thetaSum F (Φs i)) :=
    hasSum_sum fun i hi => ((hT F E σ d _ (h i hi)).1).mul_left (c i)
  simp only [lin_T_sum] at h1
  exact h1.unique h2

theorem lin_I_sum (hT : TTheta) (hA : ThetaAuto) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn)
    (h : ∀ i ∈ s, Φs i ∈ d.sch) (x : d.G) : d.I (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.I (Φs i) x := by
  have e : ∀ g : UA σ d.A.J, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) =
      ∑ i ∈ s, c i * thetaSum F (d.om x (d.S g (Φs i))) := by
    intro g

    rw [map_sum, map_sum]
    simp only [map_smul]
    exact lin_thetaSum_sum d hT s c (fun i => d.om x (d.S g (Φs i))) fun i hi => lin_om_mem d x (lin_S_mem d g (h i hi))
  have hint : ∀ i ∈ s, IntegrableOn (fun g => thetaSum F (d.om x (d.S g (Φs i)))) d.D d.μ :=
    fun i hi => ((hA F E σ d).2.2 _ (h i hi)).1 x
  show ⨍ g in d.D, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) ∂d.μ =
    ∑ i ∈ s, c i * ⨍ g in d.D, thetaSum F (d.om x (d.S g (Φs i))) ∂d.μ
  simp only [e, setAverage_eq]
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (c i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_smul_comm]

end SDl

theorem lin_psi_meas (d : SD σ) (M : Mx F E d.n d.n) :
    Measurable (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) := by
  have key : ∀ β : nA σ d.Y d.b, d.B.ψ (-d.tt (M * β.1)) =
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) := by
    intro β

    simp only [SD.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib, lin_addChar_sum]
  rw [show (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext key]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  have hc : Continuous fun y : AE F E => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * y))) :=
    d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg
  exact hc.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtype_coe))

theorem lin_fc_sum (hLB : LamBd) (d : SD σ) {nb lam 𝓖} (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    (T : nF σ d.Y d.b) (hND : IsND T) (x : d.G) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → d.G → ℂ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, ∀ γ ∈ rat2 σ d.Y, ∀ g, f i (γ * g) = f i g) :
    fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, c i • f i) T x = ∑ i ∈ s, c i * fc d.B.ψ d.b nb lam 𝓖 (f i) T x := by
  classical
  obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
  have hfun : ∀ s : Finset ι, (∑ i ∈ s, c i • f i) = fun a => ∑ i ∈ s, c i * f i a := by
    intro s; funext a; simp [Finset.sum_apply]
  have hcs : ∀ s : Finset ι, Continuous (∑ i ∈ s, c i • f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      change Continuous (fun _ : d.G => (0 : ℂ))
      exact continuous_const
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (continuous_const.smul (hc i)).add ih
  have his : ∀ s : Finset ι, ∀ γ ∈ rat2 σ d.Y, ∀ g, (∑ i ∈ s, c i • f i) (γ * g) = (∑ i ∈ s, c i • f i) g := by
    intro s γ hγ g; rw [hfun s]; exact Finset.sum_congr rfl fun i _ => by rw [hi i γ hγ g]
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    simp only [one_smul, add_zero, one_mul] at h0
    simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hlin (c j) (f j) _ (hc j) (hcs s) (hi j) (his s), ih]

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def toMx {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) : Mx F E m n := Matrix.of fun a j => Y j a

def IsPureBy {d : SD σ} (R : RD d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)

def Jd (d : SD σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ

def Td {n : ℕ} (η : E) (T₀ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E := ((-2 * η) • T₀)ᵀ

structure Rel (d : SD σ) (R : RD d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : nF σ d.Y d.b) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1

def RelEx : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ, d.KFin Φ → ∀ P gf, IsPureBy R Φ P gf →
  ∀ x t u, inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 → ∀ T : nF σ d.Y d.b, IsND T →
  ∃ (η : E) (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)),
    Rel d R x t u T η T₀ hOf θ fr g ∧ (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) ∧ (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧
    (Td η T₀).det ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (Jd d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (Jd d η) (AF F) d.B.ψ d.n μ ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν

def HeightDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) x t u T η T₀ hOf θ fr g, Rel d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹

def MeasDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) x t u T η T₀ hOf θ fr g, Rel d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ν,
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν → MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (Jd d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc

def ThetaDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (Jd d η) μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (Jd d η) μH 𝓕 ∧
    ∀ (T : nF σ d.Y d.b) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m (Jd d η) (fun Y => d.T Φ (toMx Y))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) X = Td η T₀})

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_countableE : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem meas_herm_top' (d : SD σ) : IsTopologicalAddGroup (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.n) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.n → Fin d.n → E))
  refine ⟨inferInstance, (hcl d.n).locallyCompactSpace,
    inferInstanceAs (SecondCountableTopology ((HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n : Set (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))))),
    ⟨rfl⟩, ?_⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.n) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : MeasP.ratHerm F E σ d.n =>
    (⟨x.1.1, AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)

theorem meas_mx_top' (d : SD σ) : IsTopologicalAddGroup (Mx F E d.m d.n) ∧ LocallyCompactSpace (Mx F E d.m d.n) ∧
    SecondCountableTopology (Mx F E d.m d.n) ∧ BorelSpace (Mx F E d.m d.n) ∧ Countable d.ratM := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.m) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.m → Fin d.n → E))
  refine ⟨inferInstance, inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E)),
    ⟨(inferInstance : BorelSpace (Fin d.m → Fin d.n → AE F E)).measurable_eq⟩, ?_⟩
  let K : AddSubgroup (Mx F E d.m d.n) :=
    (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range
  have hle : d.ratM ≤ K := by
    refine (AddSubgroup.closure_le K).mpr ?_
    rintro _ ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.m) (Fin d.n) E → Mx F E d.m d.n)).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : d.ratM =>
    (⟨x.1, AddMonoidHom.mem_range.mp (hle x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext h

end PositivityTheory.SiegelWeilFormula.KWhit

end
end
