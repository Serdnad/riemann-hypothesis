module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle873
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle641
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle785
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle382
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle305
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TranslateSumVacuumMovedByAdelicPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle875
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.VacTransNe

theorem sum_heisO_conjHalf_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → ∑ y ∈ Y, heisO ψ V W y f₀ ≠ 0 := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY hYd hYc h0
  obtain ⟨y₀, hy₀, -⟩ := hYc 0 (fun i j => mul_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  obtain ⟨p, hp⟩ := hP.2.2.2.2.2.2.2.2.2.norm.1
  have h := GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y
    (fun y hy => (hY y hy).1) hYd p.1 p.2 hp
  rw [h0] at h
  have hz : nrm2 p.1 p.2 (0 : WO V W → ℂ) = 0 := by
    unfold nrm2
    simp
  rw [hz] at h
  have hc : Y.card = 0 := by exact_mod_cast h.symm
  exact Finset.card_ne_zero_of_mem hy₀ hc

end GlobalTheory.VacTransNe

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.PartialBlock

open GroundTheory.Automorphic.FourierWhittaker (partialCoeff_self coe_blockGL blockMat_apply diagonal_blockGL)

variable {E : Type} [Field E] [NumberField E]

theorem good_top {ψ : AddChar (Ad E) ℂ} {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) :
    Good ψ k φ := by
  refine ⟨hφ, fun γ _ g => hl γ g, ?_, hv⟩
  intro j hj y g
  have he : IsEmpty (UnipotentBlockColumnIndex (k + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  have hd : dot (eLast (k + 1) j) (0 : UnipotentBlockColumnIndex (k + 1) j j → Ad E) = 0 := by simp [dot]
  rw [hd, AddChar.map_zero_eq_one, one_mul]
  unfold blkU
  rw [posU_zero, one_mul]

theorem good_partialCoeff {k : ℕ} {φ : GA E (k + 1) → ℂ} (hφ : Continuous φ)
    (hl : ∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g)
    (hv : ∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0)
    {m : ℕ} (hm : m ≤ k) : Good (GlobalTheory.StdCharConductor.psi E) m (partialCoeff φ (m + 1)) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [partialCoeff_self]; exact good_top hφ hl hv
  | of_succ m hm ih =>
    rw [← GlobalTheory.WhitCols.colT_partialCoeff hφ (fun γ _ g => hl γ g) (by omega : m + 1 < k + 1)]
    exact GlobalTheory.CuspRep.Generic.good_colT (GlobalTheory.StdCharConductor.stdPsi_psi E) (by omega) ih

theorem blkU_entry {R : Type} [CommRing R] {a r m : ℕ} (y : UnipotentBlockColumnIndex a r m → R) (i k : Fin a) :
    (blkU y : GL (Fin a) R).val i k = (1 : Matrix (Fin a) (Fin a) R) i k +
      if h : (i : ℕ) < r ∧ r ≤ (k : ℕ) ∧ (k : ℕ) ≤ m then y ⟨(i, k), h⟩ else 0 := by
  rw [← posM_block_entry]; rfl

def blkEquiv {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : UnipotentBlockColumnIndex n r m ≃ UnipotentBlockColumnIndex (m + 1) r m where
  toFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  invFun t := ⟨(⟨t.1.1.1, by have := t.2; omega⟩, ⟨t.1.2.1, by have := t.2; omega⟩), t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def blkHom {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) : (UnipotentBlockColumnIndex (m + 1) r m → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex n r m → Ad E) where
  toFun x := fun t => x (blkEquiv h r t)
  invFun y := fun i => y ((blkEquiv h r).symm i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem blkHom_mem_iff {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    blkHom h r x ∈ ratV E (UnipotentBlockColumnIndex n r m) ↔ x ∈ ratV E (UnipotentBlockColumnIndex (m + 1) r m) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun i => c ((blkEquiv h r).symm i), funext fun i => congrFun hc ((blkEquiv h r).symm i)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c (blkEquiv h r t), rfl⟩

theorem blockGL_blkU {n m : ℕ} (h : m + 1 ≤ n) (r : ℕ) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) :
    (blockGL h (blkU x) : GL (Fin n) (Ad E)) = blkU (blkHom h r x) := by
  refine Units.ext ?_
  ext i j
  rw [coe_blockGL, blockMat_apply, blkU_entry]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dite_eq_left hi, dite_eq_left hj, blkU_entry]
      congr 1
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dite_eq_left hi, dite_eq_right hj, dite_eq_right (by omega), Matrix.one_apply_ne hne, add_zero]
  · rw [dite_eq_right hi, dite_eq_right (by omega), add_zero, Matrix.one_apply]

omit [NumberField E] in
theorem isMir_blockGL {n m : ℕ} (h : m + 1 ≤ n) {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) :
    IsMir m (blockGL h γ : GL (Fin n) E) := by
  intro i j hij
  rw [coe_blockGL, blockMat_apply]
  by_cases hi : (i : ℕ) < m + 1
  · by_cases hj : (j : ℕ) < m + 1
    · rw [dite_eq_left hi, dite_eq_left hj, hγ _ _ hij]
      simp only [Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ j := fun e => hj (e ▸ hi)
      rw [dite_eq_left hi, dite_eq_right hj, Matrix.one_apply_ne hne]
  · rw [dite_eq_right hi, Matrix.one_apply]

theorem good_restrict {ψ : AddChar (Ad E) ℂ} {n m : ℕ} (h : m + 1 ≤ n) {F : GA E n → ℂ} (hF : Good ψ m F) :
    Good ψ m (fun g : GA E (m + 1) => F (blockGL h g)) := by
  refine ⟨hF.cont.comp (GlobalTheory.RSnm.continuous_blockGL h), ?_, ?_, ?_⟩
  · intro γ hγ g
    have e : (blockGL h (ratGL E (m + 1) γ) : GA E n) = ratGL E n (blockGL h γ) := (diagonal_blockGL h γ).symm
    simp only [map_mul]
    rw [e, hF.left _ (isMir_blockGL h hγ)]
  · intro j hj y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) j j) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) j) (0 : UnipotentBlockColumnIndex (m + 1) j j → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have hP := per_blk (r := r) (m := m) hF.cont (fun c g => hF.left _ (isMir_blkU c) g) (blockGL h g)
    rw [← hF.van r hr hrm (blockGL h g), ← avg_equiv _ _ _ _ (isCoLat_ratV E _) (isCoLat_ratV E _) (blkHom h r)
      (blkHom_mem_iff h r) _ hP]
    simp only [map_mul, blockGL_blkU]

theorem good_partialCoeff_blockGL : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    Good (GlobalTheory.StdCharConductor.psi E) m (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  intro E _ _ k m hmk φ hφ hl hv
  exact good_restrict _ (good_partialCoeff hφ hl hv (by omega))

end GlobalTheory.PartialBlock

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert

section Op

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def opP (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (c : WO S T →₀ ℂ) (h : GA D T) : Module.End ℂ (WO S T → ℂ) :=
  ∑ y ∈ c.support, c y • (GlobalTheory.SplitScalar.heisL ψ S T y * om (1, h))

theorem opP_apply (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (c : WO S T →₀ ℂ) (h : GA D T)
    (f : WO S T → ℂ) : opP ψ S T om c h f = comb ψ S T c (om (1, h) f) := by
  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, GlobalTheory.SplitScalar.heisL_apply, comb,
    Finsupp.sum]

theorem opP_comm {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) {e : AE D} {c : WO S T →₀ ℂ}
    (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {B : Module.End ℂ (WO S T → ℂ)} (hB : CommAt ψ S T e B)
    (hBh : ∀ f, IsThetaFunO ψ S T f → B (om (1, h) f) = om (1, h) (B f)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    B (opP ψ S T om c h f) = opP ψ S T om c h (B f) := by

  simp only [opP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, (hB _ (hpres _ _ hf)).2 y (hc y hy), hBh f hf]

theorem fin_of_half {e : AE D} (he : infPart D e = 0) {y : WO S T} (hy : IsHalf e y) : y.map (infPart D) = 0 :=
  Matrix.ext fun a b => by
    rw [Matrix.map_apply, ← hy a b, RingHom.map_mul, he, zero_mul]
    rfl

theorem opP_theta {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)) (hψ : IsStdChar D ψ (-1)) {e : AE D}
    (he : infPart D e = 0) {c : WO S T →₀ ℂ} (hc : ∀ y ∈ c.support, IsHalf e y) (h : GA D T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opP ψ S T om c h f) := by
  rw [opP_apply, comb, Finsupp.sum]
  exact theta_sum _ _ f hf fun y hy =>
    theta_smul _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_half he (hc y hy)) (hpres _ _ hf))

end Op

end GlobalTheory.DownLift.GenSplit

namespace GlobalTheory.DownLift.GenSplit

open GlobalTheory.IdemSupport GlobalTheory.DownLift.GenFinite.Inert



theorem placeOp_keep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t Sb v hv h hh c hc f hT hCl hL
  have hW := hω i t
  obtain ⟨-, -, hcA, hfin, -⟩ := GlobalTheory.PlaceTensor.idem_spec D
  have hε := (hfin v).2.2
  have hεe := placeIdem_eq hε
  have hinf := (hfin v).1
  have hce := hcA (.inl v)
  have hpres := hW.om_pres

  have hk : ∀ κ : GA D (Vc D i), SuppIn (dropPl Sb v) (Vc D i) κ → ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
      R.ωP i t (κ⁻¹, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ⁻¹, 1) φ) ∧
      R.ωP i t (κ, 1) (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (R.ωP i t (κ, 1) φ) := by
    intro κ hs φ hφ
    have h1 := suppF_of_drop hs hε
    rw [hεe] at h1
    have h2 := (suppGroup _ (1 - idem D (.inl v))).inv_mem h1
    have hcomm : ∀ k : GA D (Vc D i), ∀ ψ', R.ωP i t (k, 1) (R.ωP i t (1, h) ψ') = R.ωP i t (1, h) (R.ωP i t (k, 1) ψ') := by
      intro k ψ'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
        one_mul, mul_one, one_mul]
    exact ⟨opP_comm hpres hc h (commAt_om hW h2) (fun ψ' _ => hcomm _ ψ') hφ,
      opP_comm hpres hc h (commAt_om hW h1) (fun ψ' _ => hcomm _ ψ') hφ⟩
  have hth := opP_theta hpres hW.std hinf hc h hT.1
  rw [← opP_apply]
  refine ⟨⟨hth, fun κ hκ hs => ?_⟩, fun PP a ha tr z hz hov κ hκ hsup => ?_, ⟨hth, fun c' hc' h0 => ?_⟩⟩
  · rw [(hk κ hs f hT.1).2, hT.2 κ hκ (suppIn_of_drop hs), map_smul]
  · obtain ⟨w, hw, how⟩ := hov
    have h0 := hCl PP a ha tr z hz ⟨w, (mem_dropPl.1 hw).2, how⟩ κ hκ fun g hg => suppIn_of_drop (hsup g hg)
    unfold avgW at h0 ⊢

    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h0, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : mirC R i PP a tr z g = 0
    · rw [hg, zero_mul, zero_smul, zero_smul, map_zero]
    · rw [map_smul, (hk (κ g) (hsup g hg) f hT.1).1]
  ·
    have hu : ∀ u ∈ c'.support, ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) φ →
        heisO R.ψ _ _ u (opP R.ψ _ _ (R.ωP i t) c h φ) = opP R.ψ _ _ (R.ωP i t) c h (heisO R.ψ _ _ u φ) := by
      intro u hu φ hφ
      have hoff := hc' u hu
      have he0 : idem D (.inl v) • u = 0 := Matrix.ext fun a b => by
        rw [Matrix.smul_apply, smul_eq_mul, ← hεe]
        exact hoff.2 v hv _ hε a b
      have hact : actO (Vc D i) (Wc D i) 1 h u = u := by
        have hM : Formalism.L2.Theta.mt (Wc D i) h - 1 = idem D (.inl v) • (Formalism.L2.Theta.mt (Wc D i) h - 1) :=
          Matrix.ext fun a b => (hh a b).symm
        rw [actO, inv_one, mt_one, Matrix.mul_one]
        conv_lhs => rw [← sub_add_cancel (Formalism.L2.Theta.mt (Wc D i) h) 1]
        rw [Matrix.add_mul, Matrix.one_mul, hM, Matrix.smul_mul, ← Matrix.mul_smul, he0, Matrix.mul_zero, zero_add]
      have := opP_comm hpres hc h (commAt_heis hW.std hce hoff.1 he0)
        (fun ψ' hψ' => by rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, hW.om_heis _ _ _ _ hψ', hact]) hφ
      rwa [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply] at this
    have h1 := hL.2 c' hc' h0
    rw [← map_zero (opP R.ψ _ _ (R.ωP i t) c h), ← h1, map_finsuppSum]
    refine Finset.sum_congr rfl fun u hu' => ?_
    dsimp only
    rw [map_smul, hu u hu' f hT.1]

end GlobalTheory.DownLift.GenSplit
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum



theorem _root_.GlobalTheory.T.translateSum_vacuum_moved_by_adelicPair : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r : ℕ) (hr : W.rank = r) (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), l₂.M ∣ bad → SplitOffBad V bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ (Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E) (γ : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : (Fin V.rank → LevQ Dw l₂) → WO V W), IsRoots l₂ (latR hr (latG W k)) mk N Y → (∀ q, colsR hr (γ q) = Y q ∧ IsFinOf V W (γ q) (u q)) → ∀ w : (Fin V.rank → LevQ Dw l₂) → ℂ, IsThetaFunO ψ V W (transSum ψ V W l₂ ι e f₀ w) ∧ om (h, k) (transSum ψ V W l₂ ι e f₀ w) = ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l₂, w q • heisO ψ V W (u q) (om (h, k) f₀) := by
  first | exact @GlobalTheory.AdTh.MovedSum.moved_transSum | exact GlobalTheory.AdTh.MovedSum.moved_transSum | (intros; apply GlobalTheory.AdTh.MovedSum.moved_transSum <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.realPoint_acts_on_thetaFockVacua_by_det_power : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (p : ℕ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ τ, IsONBasis (gramAt D W τ) (sW τ) (BW τ) p) →
    ∃ k : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f →
      (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f) →
      om (a, 1) f = (∏ τ, (Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a)).det ^ k τ) • f := by
  first | exact @GlobalTheory.RealVacPow.vacuum_det_power | exact GlobalTheory.RealVacPow.vacuum_det_power | (intros; apply GlobalTheory.RealVacPow.vacuum_det_power <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuumTranslates_conjHalf_sq_norm_eq_card : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∀ (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → ∀ (μ : MeasureTheory.Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → nrm2 μ 𝓕 (∑ y ∈ Y, heisO ψ V W y f₀) = Y.card := by
  first | exact @GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | exact GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt | (intros; apply GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt <;> assumption)
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay

theorem growth_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF g
  obtain ⟨C, N, hC⟩ := hF g
  set I := ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν with hI
  refine ⟨|C| * ((a : ℝ) + 1) ^ N * I, N, fun y => ?_⟩
  have hint := (hk.2.2 N).const_mul (|C| * ((a : ℝ) + 1) ^ N * height y ^ N)
  have hb : ∀ x, ‖k x * F (g * infGL E a y * infGL E a (γ x))‖ ≤
      |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
    intro x
    rw [mul_assoc g, ← map_mul, norm_mul]
    have h1 := hC (y * γ x)
    have hm := GlobalTheory.HCF.ModGrowth.height_mul_le y (γ x)
    have hy := one_le_height y
    have hg := one_le_height (γ x)
    have hz := one_le_height (y * γ x)
    have e1 : height (y * γ x) ^ N ≤ (((a : ℝ) + 1) * (height y * height (γ x))) ^ N :=
      pow_le_pow_left₀ (by linarith) hm N
    have e2 : ‖F (g * infGL E a (y * γ x))‖ ≤ |C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg C)))
    calc ‖k x‖ * ‖F (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N)) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
      _ = |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
          rw [mul_pow, mul_pow]; ring
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, hI]
  ring

end GlobalTheory.MSpanDecay
end
end

section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

theorem _root_.GlobalTheory.T.decaysAtShortRationalVectors_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.ShortVecDecay.Decays F → GlobalTheory.ShortVecDecay.Decays (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.RapidKernelDecay.decays_integral | exact GlobalTheory.RapidKernelDecay.decays_integral | (intros; apply GlobalTheory.RapidKernelDecay.decays_integral <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.GlobalTheory.T.rankinSelbergThetaIntegral_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ)
    (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (ratMirU E (m + 1) m) 𝓕P μ →
    ∀ φ φ' : GA E (m + 1) → ℂ, Measurable φ → Measurable φ' → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ γ g, φ' (ratGL E (m + 1) γ * g) = φ' g) → ∀ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), Continuous Φ → ∀ x : ℝ,
    ∫⁻ g in 𝓕P, ‖Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ)‖ₑ ∂μ ≠ ⊤ →
    Zint μ 𝓕 φ φ' Φ N x = ∫ g in 𝓕P, Psi φ φ' Φ N g (GlobalTheory.ZEul.lastRow g) * (detPow E (m + 1) x g : ℂ) ∂μ := by
  exact @GlobalTheory.ZUnfTheta.zint_eq_mirabolic
end
