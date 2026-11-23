module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle026
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  first | exact @GlobalTheory.PsiProd.psi_prod | exact GlobalTheory.PsiProd.psi_prod | (intros; apply GlobalTheory.PsiProd.psi_prod <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.mixed_projection_preserves_schwartz_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  first | exact @GlobalTheory.MixedForm.proj_schA_adm | exact GlobalTheory.MixedForm.proj_schA_adm | (intros; apply GlobalTheory.MixedForm.proj_schA_adm <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour


open Classical in
theorem factor_isAddHaar (F : Type) [Field F] [NumberField F] :
    ((Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _


open Classical in
instance measI_isAddHaar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (measI F κ).IsAddHaarMeasure := by
  haveI := factor_isAddHaar F
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

theorem eInf_continuous {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) : Continuous (fun x => eInf x y) := by
  classical
  have hT : Continuous (fun x : κ → mixedEmbedding.mixedSpace F =>
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y)) :=
    LinearMap.continuous_of_finiteDimensional ((GlobalTheory.ArchFourier.traceDot F κ).flip y)
  unfold eInf
  fun_prop

theorem norm_eInf {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : ‖eInf x y‖ = 1 := by
  unfold eInf
  rw [Complex.norm_exp]
  simp

theorem exists_fourier_measI : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Surjective ei ∧ (∀ f y, ei f y = ∫ x, f x * eInf x y ∂(measI F κ)) ∧
      ∀ (f : SInf F κ) y, Continuous (fun x => f x * eInf x y) ∧ Integrable (fun x => f x * eInf x y) (measI F κ) := by
  intro F _ _ κ _
  classical
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  obtain ⟨ei, hb, he⟩ := GlobalTheory.ArchFourier.exists_fourier_sInf F κ (measI F κ)
  refine ⟨ei, hb.2, fun f y => he f y, fun f y => ⟨f.continuous.mul (eInf_continuous y), ?_⟩⟩
  haveI : (measI F κ).HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hf : Integrable (fun x => f x) (measI F κ) := f.integrable
  exact hf.mul_bdd (eInf_continuous y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (norm_eInf x y).le)

end GlobalTheory.WeylFour
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.local_fourier_double_reflection : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  first | exact @GlobalTheory.WeylFour.LocInv.fourV_fourV | exact GlobalTheory.WeylFour.LocInv.fourV_fourV | (intros; apply GlobalTheory.WeylFour.LocInv.fourV_fourV <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

theorem _root_.GlobalTheory.T.split_unitary_lift_tendsto_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  first | exact @GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | exact GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | (intros; apply GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.continuous_unitaryGLBlockEmbedding_polynomial_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      Continuous ι := by
  first | exact @GlobalTheory.BlockForms.isBlockEmb_continuous | exact GlobalTheory.BlockForms.isBlockEmb_continuous | (intros; apply GlobalTheory.BlockForms.isBlockEmb_continuous <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ArchFourier

theorem fourier_twice_sInf : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)]
    [BorelSpace (κ → mixedEmbedding.mixedSpace F)] (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure],
    ∃ d : ℂ, d ≠ 0 ∧ ∀ (f : SInf F κ) (a : κ → mixedEmbedding.mixedSpace F),
      ∫ y, (∫ x, f x * Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) ∂μ) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ a) : ℝ)) ∂μ =
      d * f (-a) := by
  intro F _ _ κ _ _ _ μ hμ
  classical
  obtain ⟨⟨c, hc, hinv⟩, hint⟩ := GlobalTheory.fourier_inversion_haar_symm_form (-(traceDot F κ))
    (fun x y => by simp only [LinearMap.neg_apply, traceDot_comm x y])
    (fun x hx => traceDot_nondeg x (fun y => by simpa using hx y)) μ hμ
  refine ⟨(c : ℂ), by exact_mod_cast hc.ne', fun f a => ?_⟩
  have hk : ∀ x y : κ → mixedEmbedding.mixedSpace F,
      Complex.exp (2 * Real.pi * Complex.I * (((-(traceDot F κ)) x y : ℝ) : ℂ)) =
        Complex.exp (-(2 * Real.pi * Complex.I) *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y) : ℝ)) := by
    intro x y
    rw [LinearMap.neg_apply, LinearMap.neg_apply, traceDot_apply]
    push_cast
    ring_nf
  have h := hinv f f.continuous (hint f).1 (hint f).2 a
  simp only [hk] at h
  exact h

end GlobalTheory.ArchFourier
end

section

noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)
open GlobalTheory.NormDict

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsScale (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Prop :=
  r * D.host.conj r * ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E)

def coordY (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ) (r : D.host.E) (w : WO S T) :
    VC D a d :=
  fun τ i j => δ * embT D τ r * compAt θ τ w (Fin.cast hT.symm i) (Fin.cast hS.symm j)

def Reads (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) (G : VC D a d → ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
    f w = Complex.exp (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) (coordY θ hS hT δ r w) (coordY θ hS hT δ r w)) *
      G (coordY θ hS hT δ r w)

structure Setup (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E) :
    Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ
  scale : IsScale D cc r

def finPt {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z : Matrix (Fin d) (Fin a) D.host.E) :
    WO S T :=
  GlobalTheory.VacUnique.finRat S T (Matrix.of fun i j => -(r⁻¹ * z (Fin.cast hT i) (Fin.cast hS j)))

def IsFinIdl (x : (AE D)ˣ) (y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) = GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D)

def HasFinPart (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) : Prop :=
  ∀ x y, IsFinIdl x y → ((χ x : Circle) : ℂ) = ((c.f y ^ e : ℂˣ) : ℂ)

def IsCongLevel {N : ℕ} (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D N)) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ k ∈ intG D N, (∀ i j, ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    (((k : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j =
      (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s) → k ∈ J

def period (D : D7) (δ : ℂ) (r : D.host.E) (τ : D.what₂.Tau) : ℂ :=
  δ * embT D τ r / (Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℂ)

def normConst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (Real.pi / area (lamOf D cc δ)) ^ (a * n τ)

variable {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure IsStdFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  frame : IsFrame P Y
  ptA : ∀ x, GlobalTheory.BotFormula.IsFinPt Y.A (Y.ιA x) x
  ptB : ∀ h, GlobalTheory.BotFormula.IsFinPt Y.B (Y.ιB h) h

structure IsMaxLevel {P : Pair D cc δ t0 Q} (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D)))
    (μ₀ : Measure (GA D Y.B)) : Prop where
  lev : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B K₀
  mem_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ K₀ ↔ h ∈ intG D P.d
  meas : ∃ 𝓕, Links.IsMeasDef Y.B K₀ μ₀ 𝓕

structure IsExact (P : Pair D cc δ t0 Q) (X : Data P) (r : D.host.E) : Prop where
  std : IsStdFrame P X.toFrame
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  chA : HasFinPart X.χA P.W.chV P.W.ep
  chB : HasFinPart X.χB P.W.chV' (-P.W.ep')
  scale : IsScale D cc r
  read : Reads X.ψ X.θ X.rkA X.rkB cc δ r P.F X.vac
  const : X.c₁ = ∏ τ, period D δ r τ ^ (P.a * P.n τ)

theorem IsExact.setup {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E} (h : IsExact P X r) :
    Setup X.ψ X.θ X.A X.B cc δ r :=
  ⟨h.weil.std, h.inf, h.std.frame.gramA, h.std.frame.gramB, P.crv, h.scale⟩

theorem isCongLevel_intG (N : ℕ) : IsCongLevel (intG D N) := ⟨1, one_pos, fun _ hk _ => hk⟩

theorem isScale_one (D : D7) : IsScale D D.host.ccK 1 := by simp [IsScale]

end GlobalTheory.NormExact
end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem substF_invT_minor_det {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} (X : Data P)
    (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ) (τ : D.what₂.Tau) (s : Fin P.a → Fin P.d) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det) =
      MvPolynomial.C ((G τ)⁻¹.det) * MvPolynomial.rename X.var (Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)).det := by
  set M := Matrix.of fun i i' : Fin P.a =>
        (MvPolynomial.X (τ, s i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D P.a P.d) ℂ)
  set φ := GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
  set H : Matrix (Fin P.a) (Fin P.a) (MvPolynomial (FVar D X.B.rank X.A.rank) ℂ) :=
    Matrix.of fun i'' i' => MvPolynomial.C ((G τ)⁻¹ (Fin.cast X.rkA.symm i') (Fin.cast X.rkA.symm i''))
  have hH : H.det = MvPolynomial.C ((G τ)⁻¹.det) := by
    have e1 : H = (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D X.B.rank X.A.rank) ℂ).mapMatrix
        (((G τ)⁻¹.transpose).submatrix (finCongr X.rkA.symm) (finCongr X.rkA.symm)) := by
      ext i j; simp [H]
    rw [e1, ← RingHom.map_det, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
  have hM : ((φ.comp (MvPolynomial.rename X.var)).mapMatrix M) = (MvPolynomial.rename X.var).mapMatrix M * H := by
    refine Matrix.ext fun i i' => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, M, H, Matrix.of_apply, AlgHom.comp_apply,
      MvPolynomial.rename_X, φ, GlobalTheory.CompactHowe.substF_X, Data.var]
    rw [Finset.sum_eq_single (Fin.cast X.rkB.symm (s i))]
    · simp only [Matrix.one_apply_eq, one_mul, Matrix.transpose_apply]
      exact Fintype.sum_equiv (finCongr X.rkA) _ _ (fun l => by simp [mul_comm])
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  have := AlgHom.map_det (φ.comp (MvPolynomial.rename X.var)) M
  rw [AlgHom.comp_apply] at this
  rw [this, hM, Matrix.det_mul, hH, ← AlgHom.map_det, mul_comm]

end GlobalTheory.NormDict

namespace GlobalTheory.NormDict

theorem substF_invT_minorPol : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P)
    (T : Tup D P.a P.d P.n) (G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ),
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ)) (fun τ => (G τ)⁻¹.transpose)
      (MvPolynomial.rename X.var (minorPol D T)) =
      (∏ τ, ((G τ)⁻¹.det) ^ P.n τ) • MvPolynomial.rename X.var (minorPol D T) := by
  intro D cc δ t0 Q P X T G
  rw [minorPol, map_prod, map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_prod, map_prod]
  simp only [substF_invT_minor_det, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

end GlobalTheory.NormDict
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem fock_isThetaFunO : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  intro D cc δ t0 Q P X hX T
  exact Formalism.IndefR.Fin.ptStable D X.ψ X.θ hX.2.weil.std hX.2.inf X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) X.vac _ hX.2.vac_theta

end GlobalTheory.NormDict
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.RallisEuler


open GlobalTheory.LFun in
theorem trivPar_euler : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  intro D χ Sf n hU
  refine ⟨(n : ℝ) / 2 + 1, fun s hs => ?_⟩
  have hs' : (n : ℝ) / 2 + 1 < s.re := hs
  set T := above D.host.E (Sf : Set (FinPl D)) with hT

  have hc : ∀ i ∈ Finset.range n, HasProd (fun w : {w // w ∉ T} => locL (charFam χ⁻¹) w.1 (s + (n : ℂ) / 2 - i))
      (charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
    refine (converges_charFam T χ⁻¹ ?_).hasProd
    simp
    linarith
  have hp := hasProd_prod hc
  show (∏ i ∈ Finset.range n, charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) =
    LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)
  rw [← hp.tprod_eq]
  unfold LSD LSTw LS eulerProd
  refine tprod_congr fun w => ?_
  have hw : UnrAt χ⁻¹ w.1 := (hU w.1 w.2).inv
  rw [GlobalTheory.BottomRallis.trivPar, twist_segFam, locL_segFam']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [locL, locL, charFam_of_unrAt hw, val_inv]
  congr 2
  · simp
  · congr 1
    push_cast
    ring

end GlobalTheory.RallisEuler
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem conjW_props : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  intro F E _ _ _ _ _ σ B hB v w hw
  have h := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have hc : GlobalTheory.LFun.IsConjAt σ h (GlobalTheory.InertBigCell.conjW σ hw) := fun y =>
    congrArg (fun z => GlobalTheory.LFun.toCompl h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z))
      ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm_apply_apply y)
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨hcc, -⟩ := hU
  refine ⟨hcc, fun x hx => GlobalTheory.LFun.InertChart.conj_mem hw hc hx, ?_,
    fun e => GlobalTheory.LFun.InertChart.conj_algebraMap hc e⟩
  have h2 := GlobalTheory.LFun.complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
  rw [GlobalTheory.LFun.complMap_algebraMap] at h2
  rwa [map_inv₀, map_inv₀, map_ofNat, map_ofNat] at h2

end GlobalTheory.InertBigCell
end
