module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle196
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle195
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDesc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.Smooth

theorem isOpen_GLs' (n : ℕ) : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

theorem continuous_cm' (n : ℕ) : Continuous (cm (n := n)) := by
  unfold cm
  exact continuous_finsetSum _ fun p _ => (continuous_apply p).smul continuous_const

theorem cm_zero' (n : ℕ) : cm (n := n) 0 = 0 := by
  simp [cm]

def mulRight' {n : ℕ} (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem contDiffOn_fderiv_apply' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {A : E → E} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply hA

theorem Rw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih (mulRight' (bs p)).contDiff.contDiffOn

theorem Dw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih contDiffOn_const

theorem smooth_all : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) :=
  fun n => ⟨isOpen_GLs' n, continuous_cm' n, cm_zero' n, fun _ _ _ _ hf =>
    ⟨Rw_contDiffOn' hf, Dw_contDiffOn' hf⟩⟩

end GlobalTheory.CompanionTheory.SobGL.Smooth
end
end

section

noncomputable section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_contDiffOn differentiableAt_of_smooth isOpen_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact Rd_contDiffOn (bs p) ih

theorem rwLin : RwLin := by
  intro n V W _ _ _ _ ι _ L f hf w
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    have hs : ∀ i, ContDiffOn ℝ ∞ (Rw w (f i)) (GLs n) := fun i => word_smooth (hf i) w
    have e : Rw w (fun y => ∑ i, L i (f i y)) =ᶠ[𝓝 x] fun y => ∑ i, L i (Rw w (f i) y) :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hx) fun y hy => ih y hy
    have hd : ∀ i, HasFDerivAt (fun y => L i (Rw w (f i) y))
        ((L i).comp (fderiv ℝ (Rw w (f i)) x)) x := fun i =>
      (L i).hasFDerivAt.comp x (differentiableAt_of_smooth (hs i) hx).hasFDerivAt
    have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i).fderiv
    show fderiv ℝ (Rw w fun y => ∑ i, L i (f i y)) x (x * bs p) =
      ∑ i, L i (fderiv ℝ (Rw w (f i)) x (x * bs p))
    rw [e.fderiv_eq]
    refine (DFunLike.congr_fun hsum (x * bs p)).trans ?_
    exact ContinuousLinearMap.sum_apply _ _ _

end GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

variable {R : Type} [CommRing R]

def colHMap {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (q : ℕ) :
    Cx.Hom (colH K q) (colH L q) (RingHom.id R) where
  f p := (φ.col p).mapH q
  comm p x := by
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj (K.col p) q).1 x
    have h1 : (K.col (p + 1)).d q ((colMap K p).f q a) = 0 := by
      rw [(colMap K p).comm, ha, map_zero]
    have h2 : (L.col p).d q ((φ.col p).f q a) = 0 := by
      rw [(φ.col p).comm, ha, map_zero]
    have h3 : (L.col (p + 1)).d q ((colMap L p).f q ((φ.col p).f q a)) = 0 := by
      rw [(colMap L p).comm, h2, map_zero]
    have h4 : (L.col (p + 1)).d q ((φ.col (p + 1)).f q ((colMap K p).f q a)) = 0 := by
      rw [(φ.col (p + 1)).comm, h1, map_zero]
    change (colMap L p).mapH q ((φ.col p).mapH q _) = (φ.col (p + 1)).mapH q ((colMap K p).mapH q _)
    rw [P.mapH_cls _ q a ha h2, P.mapH_cls _ q _ h2 h3, P.mapH_cls _ q a ha h1, P.mapH_cls _ q _ h1 h4]
    have e : (colMap L p).f q ((φ.col p).f q a) = (φ.col (p + 1)).f q ((colMap K p).f q a) := φ.ch p q a
    exact ((P.cls_surj (L.col (p + 1)) q).2.2.1 _ _ h3 h4).2 (by rw [e, sub_self]; exact Submodule.zero_mem _)

variable {C : Type 1} [Category.{0} C]

theorem restr_bij (F : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n) := by
  let E : C ⥤ Type := (Functor.const C).obj PUnit.{1}
  let G : C ⥤ E.Elements :=
    { obj := fun T => Functor.elementsMk E T PUnit.unit
      map := fun φ => ⟨φ, rfl⟩ }
  refine P.mapH_bij _ (fun k => ⟨fun x y h => ?_, fun y => ?_⟩) n
  · funext c
    exact congrFun h (c ⋙ G)
  · exact ⟨fun c => y (c ⋙ G), funext fun s => rfl⟩

variable {ι : Type}

def eTot (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) : CH.H F n ≃ₗ[R] (dbl U hU F).tot.H n :=
  (LinearEquiv.ofBijective _ (restr_bij F n)).trans
    (LinearEquiv.ofBijective _ (P.cech_desc (idxπ U hU) F (fun T x => by
      obtain ⟨α, hα⟩ := hc T
      exact ⟨⟨α, hα⟩, rfl⟩) n))

theorem col_sub (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (p q : ℕ) (hq : q ≠ a) :
    Subsingleton (((dbl U hU F).col p).H q) := by
  have := fun i => hv p i q hq
  exact (colCmp_bij U hU F p q).1.subsingleton

def eRow (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    (dbl U hU F).tot.H (a + j) ≃ₗ[R] (colH (dbl U hU F) a).H j :=
  Classical.choose (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j)

theorem eRow_clsZ (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ)
    (z : Zf (dbl U hU F) (a + j) j) :
    eRow F U hU a hv j (clsZ (dbl U hU F) (a + j) j z) = leadE (dbl U hU F) j a z :=
  Classical.choose_spec (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j) z

def eCol (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ) :
    (colH (dbl U hU F) a).H j ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  LinearEquiv.ofBijective _ (P.mapH_bij (colCmp U hU F a) (fun p => colCmp_bij U hU F p a) j)

theorem eCol_cls (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ)
    (x : (colH (dbl U hU F) a).X j) (hx : (colH (dbl U hU F) a).d j x = 0)
    (h : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j ((colCmp U hU F a).f j x) = 0) :
    eCol F U hU a j ((colH (dbl U hU F) a).cls x hx) = (CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h :=
  P.mapH_cls _ j x hx h

def eDeg (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  (eTot F U hU hc (a + j)).trans ((eRow F U hU a hv j).trans (eCol F U hU a j))

theorem eDeg_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) (x : CH.H F (a + j)) :
    eDeg F U hU hc a hv j x = eCol F U hU a j (eRow F U hU a hv j (eTot F U hU hc (a + j) x)) := rfl

theorem cech_deg : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH F U a).X j)
      (h0 : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((CrystallineSemistableComparison.Pb.cechH F' U' a).cx.cls _ h1) := by
  intro R _
  refine ⟨fun F _ U hU hc a hv j => eDeg F U hU hc a hv j, ?_⟩
  intro C C' _ _ F F' ι ι' U U' hU hc hU' hc' a hv hv' m τ hτ j c h0 h1
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.cech_double_complex_map F F' U U' hU hU' m τ hτ
  obtain ⟨c₁, rfl⟩ := (colCmp_bij U hU F j a).2 c
  have hd₁ : (colH (dbl U hU F) a).d j c₁ = 0 := by
    refine (colCmp_bij U hU F (j + 1) a).1 ?_
    rw [← (colCmp U hU F a).comm, h0, map_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.T.double_complex_lead_surjective (dbl U hU F) a j
    (fun p q hq => col_sub F U hU a hv p q hq.ne) ((colH (dbl U hU F) a).cls c₁ hd₁)
  have hy : (eDeg F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h0) =
      (eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z) := by
    rw [LinearEquiv.symm_apply_eq, eDeg_apply, LinearEquiv.apply_symm_apply, eRow_clsZ, hz, eCol_cls F U hU a j c₁ hd₁ h0]
  obtain ⟨z', hz'1, y', hy', y₀, hy₀, e1, e2, e3⟩ := GlobalTheory.T.double_complex_map_lead_compat (dbl U hU F) (dbl U' hU' F') φ a j z
  show m.pull (a + j) ((eDeg F U hU hc a hv j).symm _) = (eDeg F' U' hU' hc' a hv' j).symm _
  rw [hy, LinearEquiv.eq_symm_apply, eDeg_apply]
  have h2 : eTot F' U' hU' hc' (a + j) (m.pull (a + j) ((eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z))) =
      clsZ (dbl U' hU' F') (a + j) j z' := by
    rw [hz'1, ← LinearEquiv.apply_symm_apply (eTot F U hU hc (a + j)) (clsZ (dbl U hU F) (a + j) j z)]
    simp only [LinearEquiv.symm_apply_apply]
    exact (hφ1 _ _).symm
  rw [h2, eRow_clsZ, e2]
  have h3 : (colH (dbl U hU F) a).cls y₀ hy₀ = (colH (dbl U hU F) a).cls c₁ hd₁ := e1.symm.trans hz
  have hd₂ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j c₁) = 0 := by
    rw [(colHMap φ a).comm, hd₁, map_zero]
  have h4 : (colH (dbl U' hU' F') a).cls y' hy' = (colH (dbl U' hU' F') a).cls _ hd₂ := by
    have hd₃ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j y₀) = 0 := by
      rw [(colHMap φ a).comm, hy₀, map_zero]
    have h5 := congrArg ((colHMap φ a).mapH j) h3
    rw [P.mapH_cls _ j _ hy₀ hd₃, P.mapH_cls _ j _ hd₁ hd₂] at h5
    subst e3
    exact h5
  have h6 : (colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁) =
      fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a ((colCmp U hU F a).f j c₁ (τ ∘ i)) := by
    funext i
    exact hφ2 j a c₁ i
  have h7 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j ((colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁)) = 0 := by
    rw [(colCmp U' hU' F' a).comm, hd₂, map_zero]
  rw [h4, eCol_cls F' U' hU' a j _ hd₂ h7]
  exact ((P.cls_surj (CrystallineSemistableComparison.Pb.cechH F' U' a).cx j).2.2.1 _ _ h7 h1).2 (by rw [h6, sub_self]; exact Submodule.zero_mem _)

end GlobalTheory.CompanionTheory.CechSerre
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil.Expand

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem natCast_l_acr : (l : A.Acr 1) = 0 := by
  simpa using A.pow_l_acr 1

theorem dxi_zero : A.dxi 1 0 = 1 := by
  rw [PAlg.dxi, divided_power_xi_zero, map_one]

theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = (((i + j).choose i : ℕ) : A.Acr 1) * A.dxi 1 (i + j) := by
  simp only [PAlg.dxi]
  rw [← map_mul, divided_power_xi_mul, map_mul, map_natCast]

theorem dxi_succ (m : ℕ) :
    A.dxi 1 m * A.dxi 1 1 = ((m + 1 : ℕ) : A.Acr 1) * A.dxi 1 (m + 1) := by
  rw [dxi_mul, Nat.choose_succ_self_right]

theorem dxi_one_pow (n : ℕ) : A.dxi 1 1 ^ n = (n.factorial : A.Acr 1) * A.dxi 1 n := by
  induction n with
  | zero => simp [dxi_zero]
  | succ n ih =>
    rw [pow_succ, ih, mul_assoc, dxi_succ, Nat.factorial_succ]
    push_cast
    ring

theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  have h := A.aTo1_coeff A.xi
  rw [xi_coeff_zero, toAcr_xi, map_neg] at h
  rw [← h, neg_neg]

theorem aTo1_pi_pow : A.aTo1 A.pi ^ l = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hp.pos (le_refl l)
  rw [aTo1_pi, neg_pow, dxi_one_pow, ht]
  push_cast
  rw [natCast_l_acr]
  simp

theorem exists_inv {a : ℕ} (h : ¬ l ∣ a) : ∃ m : ℕ, (m : A.Acr 1) * (a : A.Acr 1) = 1 := by
  have hp : l.Prime := Fact.out
  have hc : Nat.Coprime a l := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp.one_lt
  refine ⟨m, ?_⟩
  have e := Nat.div_add_mod (a * m) l
  rw [hm.2] at e
  have e' := congrArg (Nat.cast : ℕ → A.Acr 1) e
  push_cast at e'
  rw [natCast_l_acr, zero_mul, zero_add] at e'
  rw [mul_comm]
  exact e'.symm

theorem dxi_lq_add (q j : ℕ) (hj : j < l) :
    ∃ n : ℕ, A.dxi 1 (l * q + j) = (n : A.Acr 1) * A.dxi 1 1 ^ j * A.dxi 1 (l * q) := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨n, hn⟩ := ih (by omega)
    have hnd : ¬ l ∣ l * q + j + 1 := by
      intro h
      rw [add_assoc] at h
      have h' := (Nat.dvd_add_right (Dvd.intro q rfl)).1 h
      have := Nat.le_of_dvd (by omega) h'
      omega
    obtain ⟨m, hm⟩ := exists_inv A hnd
    refine ⟨m * n, ?_⟩
    have e := dxi_succ A (l * q + j)
    calc A.dxi 1 (l * q + (j + 1))
        = (m : A.Acr 1) * ((l * q + j + 1 : ℕ) : A.Acr 1) * A.dxi 1 (l * q + j + 1) := by
          rw [hm, one_mul]; rfl
      _ = (m : A.Acr 1) * (A.dxi 1 (l * q + j) * A.dxi 1 1) := by rw [e]; ring
      _ = _ := by rw [hn]; push_cast; ring

theorem expand_single (q : ℕ) (b : A.A) :
    A.expand (Finsupp.single q b) = A.aTo1 b * A.dxi 1 (l * q) := by
  simp [PAlg.expand]

theorem exists_dxi_eq (k : ℕ) : ∃ (b : A.A) (q : ℕ), A.dxi 1 k = A.aTo1 b * A.dxi 1 (l * q) := by
  have hp : l.Prime := Fact.out
  obtain ⟨n, hn⟩ := dxi_lq_add A (k / l) (k % l) (Nat.mod_lt _ hp.pos)
  rw [Nat.div_add_mod] at hn
  refine ⟨(n : A.A) * (-A.pi) ^ (k % l), k / l, ?_⟩
  rw [hn, map_mul, map_natCast, map_pow, map_neg, aTo1_pi, neg_neg]

theorem expand_add (c c' : ℕ →₀ A.A) : A.expand (c + c') = A.expand c + A.expand c' := by
  simp only [PAlg.expand]
  exact Finsupp.sum_add_index' (by simp) (by intro k a b; simp [add_mul])

theorem expand_smul (a : A.A) (c : ℕ →₀ A.A) : A.expand (a • c) = A.aTo1 a * A.expand c := by
  simp only [PAlg.expand]
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [smul_eq_mul, map_mul, mul_assoc]

theorem expand_surjective : Function.Surjective A.expand := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hz := mem_spanFrom_zero A z
  unfold spanFrom at hz
  change ∃ c, A.expand c = A.mkAcr 1 z
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨b, q, h⟩ := exists_dxi_eq A k
    exact ⟨Finsupp.single q b, by rw [expand_single, ← h]; rfl⟩
  | zero => exact ⟨0, by simp [PAlg.expand]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h⟩ := hx
    obtain ⟨c', h'⟩ := hy
    exact ⟨c + c', by rw [expand_add, h, h', (A.mkAcr 1).map_add]⟩
  | smul w x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨w.coeff 0 • c, ?_⟩
    rw [expand_smul, h, aTo1_coeff, Algebra.smul_def, map_mul]
    rfl

theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧
    (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧
    (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧
    ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := fun A =>
  ⟨expand_surjective A, expand_add A, expand_smul A, fun k => by
    rw [map_pow, aTo1_pi_pow, zero_mul]⟩

end GlobalTheory.CompanionTheory.PerfFil.Expand
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineLift

theorem liftEx : CrystallineSemistableComparison.E.LiftEx := by
  intro l _ H O _ X q κ C _ G D
  have key : ∀ p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y,
      (∀ T, p T ≫ D.f = (G.obj T).2.1) → ∃ Λ : Lift G D, Λ.p = p := by
    intro p hp
    have hh : ∀ {T T' : C} (φ : T ⟶ T'),
        (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) ≫ D.f = p T' ≫ D.f := by
      intro T T' φ
      rw [Category.assoc, hp, hp]
      exact congrArg Subtype.val (G.map φ).2
    have ex : ∀ {T T' : C} (φ : T ⟶ T'), ∃ w : ((G.obj T').1.obj.A)ˣ,
        (G.obj T').1.obj.sharp w = (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)) := by
      intro T T' φ
      exact H.sharp _ (G.obj T').1.property (Units.map
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom.toMonoidHom
        (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)))
    exact ⟨{ p := p, hp := hp, w := fun φ => (ex φ).choose, hw := fun φ _ => (ex φ).choose_spec }, rfl⟩
  refine ⟨key, fun hE => ?_⟩
  have sec : ∀ T : C, ∃ p : Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y, p ≫ D.f = (G.obj T).2.1 := by
    intro T
    haveI := D.surj
    obtain ⟨s, hs⟩ := H.splitU _ (G.obj T).1.property (pullback D.f (G.obj T).2.1)
      (pullback.snd D.f (G.obj T).2.1) inferInstance inferInstance
    refine ⟨s ≫ pullback.fst D.f (G.obj T).2.1, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  choose p hp using sec
  obtain ⟨Λ, -⟩ := key p hp
  exact ⟨Λ⟩

end GlobalTheory.CompanionTheory.LineLift
end
