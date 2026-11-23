module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle142
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.schrodinger_preserves_schwartz_bruhat : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  first | exact @GlobalTheory.SchrSB.schr_mem_SB | exact GlobalTheory.SchrSB.schr_mem_SB | (intros; apply GlobalTheory.SchrSB.schr_mem_SB <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma vecMulVec_mul_transpose' {m k : Type} [Fintype k] {R : Type} [CommRing R] (p : m → R) (q : k → R)
    (M : Matrix k k R) : Matrix.vecMulVec p q * Mᵀ = Matrix.vecMulVec p (M *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {q : Fin d ⊕ Fin d → AE F E} (hq : q ∈ GlobalTheory.DblVac.latD W v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latDbl X W v := by
  refine ⟨?_, ?_⟩
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₁ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inl) := by
      ext i j; simp [Matrix.toCols₁, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.1
  · have : (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q).toCols₂ =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (q ∘ Sum.inr) := by
      ext i j; simp [Matrix.toCols₂, Matrix.vecMulVec_apply]
    rw [this]; exact GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hq.2

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hM : ∀ q ∈ GlobalTheory.DblVac.latD W v, M *ᵥ q ∈ GlobalTheory.DblVac.latD W v) :
    ∀ γ ∈ latDbl X W v, γ * Mᵀ ∈ latDbl X W v := by

  let φ₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols γ 0 : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  let φ₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun γ : Matrix (Fin n) (Fin d) (AE F E) =>
      (Matrix.fromCols 0 γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) * Mᵀ) (by
      intro a b; rw [← Matrix.add_mul]; congr 1; ext i (j | j) <;> simp)
  have key : ∀ (φ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)),
      (∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ x ∈ X.L, ∀ y ∈ W.L,
        ∃ q ∈ GlobalTheory.DblVac.latD W v,
          φ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) →
      latAtV X W v ≤ (latDbl X W v).comap φ := by
    intro φ hφ
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    obtain ⟨q, hq, he⟩ := hφ a ha hai x hx y hy
    show φ _ ∈ latDbl X W v
    rw [he]; exact vecMulVec_mem_latDbl X W v hx hq
  have gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt W v := fun a ha hai y hy =>
    AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, rfl⟩
  have h₁ : latAtV X W v ≤ (latDbl X W v).comap φ₁ := by
    refine key φ₁ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim (a • fun i => inclR (F := F) (AF F) (y i)) 0, hM _ ?_, ?_⟩
    · exact ⟨by simpa using gen a ha hai y hy, by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₁, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  have h₂ : latAtV X W v ≤ (latDbl X W v).comap φ₂ := by
    refine key φ₂ fun a ha hai x hx y hy => ⟨M *ᵥ Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (y i)), hM _ ?_, ?_⟩
    · exact ⟨by simpa using (GlobalTheory.InertSph.latAt W v).zero_mem, by simpa using gen a ha hai y hy⟩
    · rw [← vecMulVec_mul_transpose']
      simp only [φ₂, AddMonoidHom.mk'_apply]
      congr 1
      rw [GlobalTheory.InertSphStab.incM_vecMulVec, GlobalTheory.InertSphStab.smul_vecMulVec]
      ext i (j | j) <;> simp [Matrix.vecMulVec_apply]
  intro γ hγ
  have hsplit : γ * Mᵀ = φ₁ γ.toCols₁ + φ₂ γ.toCols₂ := by
    simp only [φ₁, φ₂, AddMonoidHom.mk'_apply]
    rw [← Matrix.add_mul]
    congr 1
    ext i (j | j) <;> simp [Matrix.toCols₁, Matrix.toCols₂]
  rw [hsplit]
  exact (latDbl X W v).add_mem (h₁ hγ.1) (h₂ hγ.2)

end GlobalTheory.DblVacStab

theorem GlobalTheory.DblVac.kD_stab_latDbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v, ∀ γ ∈ latDbl X W v,
      γ * (GlobalTheory.DblVac.matD g)ᵀ ∈ latDbl X W v ∧ γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ latDbl X W v := by
  intro F E _ _ _ _ _ σ n d X W v g hg γ hγ
  exact ⟨GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).1) γ hγ,
    GlobalTheory.DblVacStab.mul_transpose_mem_latDbl X W v _ (fun q hq => (hg.2 q hq).2) γ hγ⟩
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.InertLagChar.LinForm

theorem hasCompactSupport_comp_of_leftInverse {X Y M : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    [Zero M] {f : X → Y} {l : Y → X} (hl : Continuous l) (hlf : ∀ x, l (f x) = x) {g : Y → M}
    (hg : HasCompactSupport g) : HasCompactSupport (g ∘ f) := by
  refine IsCompact.of_isClosed_subset (hg.image hl) isClosed_closure ?_
  refine closure_minimal ?_ (hg.image hl).isClosed
  intro x hx
  exact ⟨f x, subset_tsupport _ hx, hlf x⟩

theorem integrable_of_cont_cs {X : Type} [TopologicalSpace X] (μ : @Measure X (borel X))
    [IsFiniteMeasureOnCompacts μ] {f : X → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f μ := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  exact hf.integrable_of_hasCompactSupport hcs

end GlobalTheory.InertLagChar.LinForm

open GlobalTheory.InertLagChar.LinForm in
theorem GlobalTheory.InertLagChar.lagInt_linForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  intro F _ _ v κ _ ψ hψ μ hμ N ν hν j hj hdiag

  have hd : Continuous (fun x : κ → Fv F v => (Sum.elim x x : κ ⊕ κ → Fv F v)) := by
    refine continuous_pi fun i => ?_
    cases i <;> exact continuous_apply _
  have hdl : Continuous (fun z : κ ⊕ κ → Fv F v => fun i => z (Sum.inl i)) :=
    continuous_pi fun i => continuous_apply _

  have hin : ∀ w : (κ → Fv F v) × (κ → Fv F v), ∀ Φ ∈ SB (κ ⊕ κ → Fv F v),
      Integrable (fun x => schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x)) μ := by
    intro w Φ hΦ
    have hs := GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ hΦ
    exact integrable_of_cont_cs μ (hs.1.continuous.comp hd)
      (hasCompactSupport_comp_of_leftInverse hdl (fun x => rfl) hs.2)
  have hschr_add : ∀ w (Φ Φ' : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (Φ + Φ') = schr ψ w Φ + schr ψ w Φ' := by
    intro w Φ Φ'; funext x; simp [schr, mul_add]
  have hschr_smul : ∀ w (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), schr ψ w (c • Φ) = c • schr ψ w Φ := by
    intro w c Φ; funext x; simp [schr]; ring
  have hdiag_add : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), ∀ Φ' ∈ SB (κ ⊕ κ → Fv F v),
      diagW ψ μ (Φ + Φ') = diagW ψ μ Φ + diagW ψ μ Φ' := by
    intro Φ hΦ Φ' hΦ'
    funext w
    simp only [diagW, Pi.add_apply, hschr_add]
    exact integral_add (hin w Φ hΦ) (hin w Φ' hΦ')
  have hdiag_smul : ∀ (c : ℂ) (Φ : (κ ⊕ κ → Fv F v) → ℂ), diagW ψ μ (c • Φ) = c • diagW ψ μ Φ := by
    intro c Φ
    funext w
    simp only [diagW, Pi.smul_apply, hschr_smul, smul_eq_mul]
    exact integral_const_mul (μ := μ) c _

  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hjc : Continuous j := IsModuleTopology.continuous_of_linearMap j
  have hlc : Continuous l := IsModuleTopology.continuous_of_linearMap l
  have hlj : ∀ y, l (j y) = y := fun y => by
    have := LinearMap.congr_fun hl y
    simpa using this
  have hout : ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Integrable (fun y => diagW ψ μ Φ (j y)) ν := by
    intro Φ hΦ
    have hs := hdiag Φ hΦ
    have hcs : HasCompactSupport (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hasCompactSupport_comp_of_leftInverse (f := (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v)))
        (l := (l : (κ → Fv F v) × (κ → Fv F v) → (Fin N → Fv F v))) hlc hlj hs.2
    have hc : Continuous (diagW ψ μ Φ ∘ (j : (Fin N → Fv F v) → (κ → Fv F v) × (κ → Fv F v))) :=
      hs.1.continuous.comp hjc
    exact integrable_of_cont_cs ν hc hcs
  let f : SB (κ ⊕ κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => lagInt ψ μ ν j Φ.1
      map_add' := by
        intro Φ Φ'
        simp only [Submodule.coe_add, lagInt, hdiag_add _ Φ.2 _ Φ'.2, Pi.add_apply]
        exact integral_add (hout _ Φ.2) (hout _ Φ'.2)
      map_smul' := by
        intro c Φ
        simp only [Submodule.coe_smul, lagInt, hdiag_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul (μ := ν) c _ }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  exact ⟨g, fun Φ hΦ => LinearMap.congr_fun hg ⟨Φ, hΦ⟩⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolBox

variable {D : D7}

theorem rp_eq_one (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (k : GA D V) (hk : k ∈ GfC V) : rp k = 1 := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  have h1 : infMat D.sp.cm.sig V.gram (θ ρ) k = 1 := by
    have h2 := congrArg Units.val ((MonoidHom.mem_ker).1 hk)
    show (Units.val (infHom V k)).map (θ ρ) = 1
    rw [h2]
    simp
  rw [hrp, h1, Pi.one_apply, GlobalTheory.Mem.VolExists.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem rp_realElt (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (b : ∀ ρ, Upq V ρ) :
    rp (realElt θ V fun ρ => realMat V A ρ (b ρ)) = b := by
  funext ρ
  refine GlobalTheory.RealBoxMeasure.mat_cancel V hV A hA ρ ?_
  obtain ⟨C, h1, -⟩ := (GlobalTheory.Mem.SignatureFactor.exists_factor _ _ _ _ (hV (tauE D ρ))).2.2 (A ρ) (hA ρ)
  have e : UpqT.mat (b ρ) * A ρ = A ρ * (C * (UpqT.mat (b ρ) * A ρ)) := by
    rw [← Matrix.mul_assoc (A ρ), h1, Matrix.one_mul]
  rw [hrp, GlobalTheory.RealBoxMeasure.infMat_realElt θ hθ V _ (fun τ => GlobalTheory.RealBoxMeasure.realMat_mem V hV A hA τ _) ρ,
    GlobalTheory.RealBoxMeasure.realMat_of V A hA ρ _ _ e, ← e]

theorem exists_fin (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ)) (hV : V.SigOK)
    (hθ : IsInfFam θ) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (h : GA D V) :
    ∃ k : GA D V, rp k = 1 ∧ finE V k = finE V h := by
  refine ⟨(realElt θ V fun ρ => realMat V A ρ (rp h ρ))⁻¹ * h, ?_, ?_⟩
  · rw [map_mul, map_inv, rp_realElt V θ A rp hV hθ hA hrp, inv_mul_cancel]
  · rw [map_mul, map_inv, GlobalTheory.RealBoxMeasure.finE_realElt, inv_one, one_mul]

theorem meas_level (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ))
    (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V))
    (hV : V.SigOK) (hθ : IsInfFam θ) (hA : IsFrames V A) (hm : ∀ ρ, IsMinf (m ρ)) (hc : Continuous rp)
    (hrp : IsRealPart V θ A rp) (hK : IsOpen {h : GA D V | finE V h ∈ K}) (hμ : IsMeasLev V K μ)
    (B : Set (∀ ρ, Upq V ρ)) (hB : MeasurableSet B) :
    μ {h | finE V h ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  haveI := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, hsc, hbo, -⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI := hsc
  haveI := hbo
  have hBm : MeasurableSet (rp ⁻¹' B) := hc.measurable hB
  have H := GlobalTheory.RealBoxMeasure.lintegral_levelSet_eq_pi D θ hθ V hV K μ hμ A hA m hm
    ((rp ⁻¹' B).indicator 1) (measurable_one.indicator hBm) (fun g k hk => by
      have : rp (g * k) = rp g := by rw [map_mul, rp_eq_one V θ A rp hV hA hrp k hk.1, mul_one]
      exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, this, Set.mem_preimage]) rfl) hK.measurableSet
  rw [lintegral_indicator_one hBm, Measure.restrict_apply hBm] at H
  rw [← lintegral_indicator_one hB, show {h | finE V h ∈ K ∧ rp h ∈ B} = rp ⁻¹' B ∩ {h : GA D V | finE V h ∈ K} from
    Set.ext fun h => and_comm, H]
  refine lintegral_congr fun b => ?_
  exact Set.indicator_eq_indicator (by rw [Set.mem_preimage, rp_realElt V θ A rp hV hθ hA hrp]) rfl

theorem meas_translate_le : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → K ≤ K₀ → K.relIndex K₀ ≠ 0 → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ (K.relIndex K₀ : ℝ≥0∞) * Measure.pi m B := by
  intro D V θ A m rp K K₀ μ hV hθ hA hm hc hrp _ hi hK hμ g _ B hB
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := hμ.1
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hi⟩
  haveI : Fintype (K₀ ⧸ K.subgroupOf K₀) := Fintype.ofFinite _
  let S : (K₀ ⧸ K.subgroupOf K₀) → Set (GA D V) := fun q =>
    {h | (∃ hh : finE V (g⁻¹ * h) ∈ K₀, (QuotientGroup.mk ⟨_, hh⟩ : K₀ ⧸ K.subgroupOf K₀) = q) ∧ rp h ∈ B}
  have hS : ∀ q, μ (S q) ≤ Measure.pi m B := by
    intro q
    rcases (S q).eq_empty_or_nonempty with h0 | ⟨h₀, ⟨hh₀, hq₀⟩, -⟩
    · rw [h0, measure_empty]; exact zero_le
    obtain ⟨k, hk1, hk2⟩ := exists_fin V θ A rp hV hθ hA hrp h₀
    rw [← meas_level V θ A m rp K μ hV hθ hA hm hc hrp hK hμ B hB, ← measure_preimage_mul μ k⁻¹ {h | finE V h ∈ K ∧ rp h ∈ B}]
    refine measure_mono ?_
    rintro h ⟨⟨hh, hq⟩, hb⟩
    have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hq₀.trans hq.symm))
    show finE V (k⁻¹ * h) ∈ K ∧ rp (k⁻¹ * h) ∈ B
    refine ⟨?_, ?_⟩
    · have h2 : finE V (k⁻¹ * h) = (finE V (g⁻¹ * h₀))⁻¹ * finE V (g⁻¹ * h) := by
        simp only [map_mul, map_inv, hk2]; group
      rw [h2]; exact h1
    · rwa [map_mul, map_inv, hk1, inv_one, one_mul]
  calc μ {h | finE V (g⁻¹ * h) ∈ K₀ ∧ rp h ∈ B} ≤ μ (⋃ q, S q) :=
        measure_mono fun h hh => Set.mem_iUnion.2 ⟨_, ⟨hh.1, rfl⟩, hh.2⟩
    _ ≤ ∑ q, μ (S q) := measure_iUnion_fintype_le μ S
    _ ≤ ∑ _q : K₀ ⧸ K.subgroupOf K₀, Measure.pi m B := Finset.sum_le_sum fun q _ => hS q
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

end GlobalTheory.CovTop.VolBox
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)),
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧ GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  first | exact @GlobalTheory.VacShape.exists_at_coBar_eq | exact GlobalTheory.VacShape.exists_at_coBar_eq | (intros; apply GlobalTheory.VacShape.exists_at_coBar_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.latticePairingTrivialMatrices_sub_mem : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  first | exact @GlobalTheory.VacShapeBd.bd_sub | exact GlobalTheory.VacShapeBd.bd_sub | (intros; apply GlobalTheory.VacShapeBd.bd_sub <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.span_realPoints_weightRepresentation_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), Submodule.span ℂ (Set.range ((wInf lam).comp (infU E n).subtype)) = ⊤ := by
  first | exact @GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | exact GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU | (intros; apply GlobalTheory.BCT.TrKer.span_range_wInf_comp_infU <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_sum_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank | exact GlobalTheory.FunObj.squareTriple_sig_rank | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

theorem _root_.GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  first | exact @GlobalTheory.FunObj.squareTriple_sig_rank_lt | exact GlobalTheory.FunObj.squareTriple_sig_rank_lt | (intros; apply GlobalTheory.FunObj.squareTriple_sig_rank_lt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.standard_adelic_character_nontrivial_at_places : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  first | exact @GlobalTheory.PsiNontriv.psiAt_ne_one | exact GlobalTheory.PsiNontriv.psiAt_ne_one | (intros; apply GlobalTheory.PsiNontriv.psiAt_ne_one <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_idempotent_conjugation_sign : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∃ f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  first | exact @GlobalTheory.SwapAtSplit.exists_swap_elt | exact GlobalTheory.SwapAtSplit.exists_swap_elt | (intros; apply GlobalTheory.SwapAtSplit.exists_swap_elt <;> assumption)
end
