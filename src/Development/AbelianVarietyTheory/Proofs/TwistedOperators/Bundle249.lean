module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExist
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjPlace

theorem conjI_eq_map {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) :
    GlobalTheory.SW.conjI P = P.map (IsCMField.ringOfIntegersComplexConj E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map, Set.image]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, by rw [IsCMField.coe_ringOfIntegersComplexConj]; rfl⟩

theorem exists_conj_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E), ∃ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.asIdeal = conjI PP.asIdeal ∧ Formalism.IndefR.Lev.IsConjPl PP' PP := by
  intro D PP
  let σ := IsCMField.ringOfIntegersComplexConj D.host.E
  haveI : (PP.asIdeal.map σ).IsPrime := Ideal.map_isPrime_of_equiv σ
  have hne : PP.asIdeal.map σ ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective σ.injective]
    exact PP.ne_bot
  refine ⟨⟨PP.asIdeal.map σ, this, hne⟩, (conjI_eq_map PP.asIdeal).symm, ?_⟩
  intro c hc
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv σ c).1 hc
  refine ⟨b, hb, ?_⟩
  show ((b : 𝓞 D.host.E) : D.host.E) = star (((σ b : 𝓞 D.host.E)) : D.host.E)
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  exact (IsCMField.complexConj_apply_apply D.host.E _).symm

end GlobalTheory.ConjPlace
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameDecomp

theorem hermC_mulVec {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (x *ᵥ a) (x *ᵥ b) = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
  unfold hermC
  calc ∑ p, ∑ q, (x *ᵥ a) p * τ (G p q) * conj ((x *ᵥ b) q)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_

        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        rw [Finset.sum_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ p, ∑ i, ∑ q, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [FD.gram, Matrix.of_apply, FD.col, hermC, Finset.mul_sum, Finset.sum_mul]

theorem isometry_of_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0) (h : FD.gram τ G x = FD.gram τ G y) (v w : Fin r → ℂ) :
    hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w) = hermC τ G v w := by
  have hyu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have hback : ∀ c : Fin r → ℂ, y *ᵥ (y⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mulVec]
  calc hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w)
      = hermC τ G (x *ᵥ (y⁻¹ *ᵥ v)) (x *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = hermC τ G (y *ᵥ (y⁻¹ *ᵥ v)) (y *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [hermC_mulVec, hermC_mulVec, h]
    _ = hermC τ G v w := by rw [hback, hback]

theorem exists_real_point {D : D7} {S T : HSp D} (C : Ctx S T)
    (u : C.X.Ψ → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hu : ∀ (σ : C.X.Ψ) v w, hermC σ.1 C.X.Gm (u σ *ᵥ v) (u σ *ᵥ w) = hermC σ.1 C.X.Gm v w) :
    ∃ a ∈ GinfC T, (fun σ => (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj) = u := by
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  obtain ⟨k, hk, hkτ⟩ := GlobalTheory.FockCompare.LiftUnitary.lift_unitary D C.θ σ₀ hσ₀ T
    (fun τ => (u (C.m.e τ)).map conj) (fun τ => by
      have hcc : ((u (C.m.e τ)).map conj).map conj = u (C.m.e τ) := by
        ext i j
        simp
      simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
      rw [GlobalTheory.StabProper.unitary_iff_form, hcc]
      intro v w
      have hform := hu (C.m.e τ) v w
      rw [GlobalTheory.StabProper.hermC_eq, GlobalTheory.StabProper.hermC_eq, Equiv.symm_apply_apply] at hform
      exact hform)
  refine ⟨k, hk, ?_⟩
  funext σ
  have hcomp : compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T k) = (u σ).map conj := by
    rw [GlobalTheory.StabProper.compAt_eq, ← GlobalTheory.FockCompare.RealAction.infMat_eq, hkτ, Equiv.apply_symm_apply]
  rw [hcomp]
  ext i j
  simp

theorem frame_decomp : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  intro D S T C B hB x hx
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  obtain ⟨hon, hbB, hxeq, -, -⟩ := hob x hx
  have hz : IsONFr C.X (C.xB B) := GlobalTheory.Ker.ONBasis.isONFr_xB C hB
  have hzdom : C.xB B ∈ C.X.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X hz
  have hdet : ∀ σ, (FD.mat (C.xB B) σ).det ≠ 0 := fun σ => (hzdom σ).1
  obtain ⟨a, ha, hau⟩ := exists_real_point C
    (fun σ => FD.mat (o x) σ * (FD.mat (C.xB B) σ)⁻¹)
    (fun σ v w => isometry_of_gram_eq σ.1 C.X.Gm (FD.mat (o x) σ) (FD.mat (C.xB B) σ) (hdet σ)
      (by rw [hon σ, hz σ]) v w)
  refine ⟨a, ha, b x, hbB, ?_⟩
  have hmove : C.xB (C.mvB a B) = o x := by
    funext σ
    have hσ := congrFun hau σ
    have hstep : FD.mat (C.xB (C.mvB a B)) σ
        = (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj * FD.mat (C.xB B) σ := by
      ext i j

      simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, FD.mat, Matrix.mul_apply, map_sum]
    rw [hσ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet σ)),
      Matrix.mul_one] at hstep
    exact hstep
  rw [hmove]
  exact hxeq

end GlobalTheory.FrameDecomp
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevMov

theorem finE_mem_St_of_isMov : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (β : GL (Fin V.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, IsMov (fmt V k) L L → Lev.finE V k ∈ Formalism.L2.DIV.St β := by
  intro D V L β hβ k hk
  have h1 := GlobalTheory.LevSplit.mem_St_iff β L hβ (Lev.finE V k)
  have h2 := GlobalTheory.LevSplit.stab_gen (GlobalTheory.LevSplit.swp D.host.F D.host.E) GlobalTheory.LevSplit.swp_bij.2 _ _
    (GlobalTheory.LevSplit.latHat_iff L) (finHom V k)
  refine h1.2 (h2.1 ?_)
  have hk' : ∀ u, u ∈ hatV L ↔ ∃ u₀ ∈ hatV L, u = (finHom V k).1 *ᵥ u₀ := hk
  intro y
  constructor
  · intro hy
    exact (hk' _).2 ⟨y, hy, rfl⟩
  · intro hy
    obtain ⟨u₀, hu₀, e⟩ := (hk' _).1 hy
    have e2 : y = u₀ := by
      have := congrArg (fun z => ((finHom V k)⁻¹).1 *ᵥ z) e
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
      exact this
    rw [e2]; exact hu₀

end GlobalTheory.LevMov
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma pos_of_isLval {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {c : Eig D} {z : ℝ} (h : IsLval R i t c z) : 0 < z := by
  obtain ⟨_, _, hL⟩ := h
  exact hL.2.1

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {p q r : Prop} (f : p → q) (k₁ : ¬p → r) (k₂ : q → r) : r := by
  by_cases hp : p
  · exact k₂ (f hp)
  · exact k₁ hp

theorem scal_of_aForm_bForm {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (SF)
    (hA : AForm R SF) (hB : BForm R SF) (hM : MatchUp R SF) : Scal R SF := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨κ₀, hκ₀, hB⟩ := hB
  have hPa : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i

  have hA' : ∀ i t c, ∃ l : ℝ, 0 < l ∧
      (∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((l : ℝ) : ℂ) • x) ∧
      ((∃ z, IsLval R i t c z ∧ l = a i * z) ∨ ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0) := by
    intro i t c
    refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hA i t c) (fun h => ?_) (fun hq => ?_)
    · have h0 : ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, x = 0 := by
        intro x hx
        by_contra hne
        exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
      refine ⟨1, one_pos, fun x hx => ?_, Or.inr h0⟩
      rw [h0 x hx]
      simp only [map_zero, smul_zero]
    · obtain ⟨z, hz, hx⟩ := hq
      exact ⟨a i * z, mul_pos (ha i) (pos_of_isLval hz), hx, Or.inl ⟨z, hz, rfl⟩⟩
  choose lam hlpos hlW hlz using hA'
  refine ⟨lam, κ₀ / (∏ i, a i), div_pos hκ₀ hPa, hlpos, hlW, ?_⟩
  intro t c x hx
  refine galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one (hM c) (fun h => ?_) (fun hW => ?_)
  ·
    have hx0 : x = 0 := by
      by_contra hne
      exact h fun hb => hne (by rw [hb] at hx; exact (Submodule.mem_bot _).mp hx)
    rw [hx0]
    simp only [map_zero, smul_zero]
  ·
    have hz' : ∀ i, ∃ z, IsLval R i t c z ∧ lam i t c = a i * z := fun i =>
      (hlz i t c).resolve_right fun h0 => hW i ((Submodule.eq_bot_iff _).mpr h0)
    choose z hz hlz' using hz'
    have key : κ₀ / (∏ i, a i) * ∏ i, lam i t c = κ₀ * ∏ i, z i := by
      rw [Finset.prod_congr rfl fun i _ => hlz' i, Finset.prod_mul_distrib, ← mul_assoc,
        div_mul_cancel₀ κ₀ hPa.ne']
    rw [key]
    exact hB t c z hz x hx

end GlobalTheory.LiftRows

end
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.RatCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (P : PPol σ n)

theorem lid_smul (c : F ⊗[F] E) (z : F ⊗[F] Fld P) :
    Algebra.TensorProduct.lid F (Fld P) (c • z) =
      Algebra.TensorProduct.lid F E c • Algebra.TensorProduct.lid F (Fld P) z := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change Algebra.TensorProduct.lid F (Fld P) (Algebra.TensorProduct.map (AlgHom.id F F)
      (IsScalarTower.toAlgHom F E (Fld P)) (a ⊗ₜ e)) = _
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply F E (Fld P)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [Field E] in
theorem inclR_lid {A : Type} [Field A] [Algebra F A] (c : F ⊗[F] A) :
    inclR F (Algebra.TensorProduct.lid F A c) = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [inclR, Algebra.TensorProduct.lid_tmul]
    change (1 : F) ⊗ₜ[F] (a • e) = a ⊗ₜ e
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

omit [Field E] in
theorem lid_inclR {A : Type} [Field A] [Algebra F A] (a : A) :
    Algebra.TensorProduct.lid F A (inclR F a) = a := by
  simp [inclR]

def tensEquiv (φ : Fld P ≃ₗ[E] (Fin n → E)) : (F ⊗[F] Fld P) ≃ₗ[F ⊗[F] E] (Fin n → F ⊗[F] E) where
  toFun z i := inclR F (φ (Algebra.TensorProduct.lid F (Fld P) z) i)
  invFun w := (Algebra.TensorProduct.lid F (Fld P)).symm (φ.symm (fun i => Algebra.TensorProduct.lid F E (w i)))
  map_add' a b := by ext i; simp
  map_smul' c z := by
    ext i
    rw [lid_smul, φ.map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply]
    rw [inclR_lid]
  left_inv z := by
    simp only [lid_inclR]
    simp
  right_inv w := by
    ext i
    simp [inclR_lid]

theorem tensEquiv_apply (φ : Fld P ≃ₗ[E] (Fin n → E)) (z : F ⊗[F] Fld P) (i : Fin n) :
    tensEquiv P φ z i = inclR F (φ (Algebra.TensorProduct.lid F (Fld P) z) i) := rfl

end GlobalTheory.RatCls

noncomputable section
namespace GlobalTheory.RatCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (P : PPol σ n)

theorem tensEquiv_tmul (φ : Fld P ≃ₗ[E] (Fin n → E)) (v : Fld P) :
    tensEquiv (F := F) P φ (1 ⊗ₜ v) = fun i => inclR F (φ v i) := by
  funext i; rw [tensEquiv_apply]; simp

theorem sigR_inclR (e : E) : sigR F σ (inclR F e) = inclR F (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    Formalism.UG.hform (sigR F σ) (JR F J) (fun i => inclR F (a i)) (fun i => inclR F (b i)) =
      inclR F (Formalism.UG.hform (σ : E →+* E) J a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.UG.hform, JR, map_sum, map_mul, sigR_inclR]

theorem trBase_tmul (w : Fld P) : trBase P F (1 ⊗ₜ w) = inclR F (Algebra.trace E (Fld P) w) := by
  simp [trBase, inclR]

end GlobalTheory.RatCls

noncomputable section
namespace GlobalTheory.RatCls

theorem hasCls_of_ratIsom : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n)
    (J : Matrix (Fin n) (Fin n) E) (φ : Fld P ≃ₗ[E] (Fin n → E)) (x : Fld P), x ≠ 0 → star' P x = x →
    (∀ y y', Formalism.UG.hform (σ : E →+* E) J (φ y') (φ y) = Algebra.trace E (Fld P) (x * y * star' P y')) →
    ∀ γ : GRat σ J, (∀ y, γ.1.1 *ᵥ φ y = φ (alpha P * y)) → ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ σ n P J φ x hx hs hφ γ hγ
  let Φ := tensEquiv (F := F) P φ
  let u : (F ⊗[F] Fld P)ˣ :=
    Units.map (Algebra.TensorProduct.lid F (Fld P)).symm.toAlgHom.toRingHom.toMonoidHom (Units.mk0 x hx)
  have hu : (u : F ⊗[F] Fld P) = 1 ⊗ₜ x := by simp [u]
  have hmem : u ∈ plusUnits P F := by
    change Units.map (sigR F (star' P)).toMonoidHom u = MonoidHom.id _ u
    ext
    simp [hu, sigR, hs]
  let xu : plusUnits P F := ⟨u, hmem⟩
  have pure : ∀ y : F ⊗[F] Fld P, ∃ v, y = 1 ⊗ₜ v := fun y =>
    ⟨Algebra.TensorProduct.lid F (Fld P) y, (inclR_lid y).symm⟩
  have hI : IsIsom P F J xu.1.1 Φ := by
    intro y y'
    obtain ⟨v, rfl⟩ := pure y
    obtain ⟨v', rfl⟩ := pure y'
    simp only [Φ, tensEquiv_tmul, hform_inclR, hφ]
    change _ = trBase P F (u.1 * 1 ⊗ₜ v * sigR F (star' P) (1 ⊗ₜ v'))
    rw [hu]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, trBase_tmul]
  refine ⟨QuotientGroup.mk xu, xu, Φ, hI, rfl, ?_⟩
  have ht : (torUnit (diagH (star' P) (one₁ P) F (alphaRat P))).1 = 1 ⊗ₜ alpha P := by
    show Matrix.det ((((alphaRat P).1 : GL (Fin 1) (Fld P)) : Matrix (Fin 1) (Fin 1) (Fld P)).map (inclR F)) = _
    rw [Matrix.det_fin_one]
    simp [alphaRat, inclR]
  apply Subtype.ext
  apply Units.ext
  show mulMat Φ (torUnit (diagH (star' P) (one₁ P) F (alphaRat P))).1 = (γ.1 : Matrix (Fin n) (Fin n) E).map (inclR F)
  rw [ht]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  obtain ⟨y, rfl⟩ := Φ.surjective w
  obtain ⟨v, rfl⟩ := pure y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulMat_mulVec, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp only [Φ, tensEquiv_tmul]
  funext i
  rw [← hγ, RingHom.map_mulVec]
  rfl

end GlobalTheory.RatCls
end
end
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftRows

theorem goodForms_definite_exist : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodVectorsDefinite → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → ∀ {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ b, ∃ i, R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ≠ ⊥ := by
  intro hGV eps heps
  obtain ⟨x₀, hx₀⟩ := hGV.2 eps heps
  refine ⟨x₀, ?_⟩
  intro D L hP heps' hxL hSz G _ _ Pl0 T A Ks _ _ _ R F hGiv b

  have hTie : GlobalTheory.GLq.ESerTie D := by
    intro k
    obtain ⟨LD, hT, hE, _⟩ := hGiv.types k
    exact ⟨LD, hT, hE⟩

  obtain ⟨kap, lam, hScal⟩ := Formalism.IndefR.Links.scal_exists (F := F) R
  have hSet : GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.HidaSetting (R.upd6 kap lam) F :=
    { lev := hGiv.core.lev
      grp := { hGiv.core.grp with }
      fam := { hGiv.core.fam with }
      models := { hGiv.core.models with }
      chain := Formalism.IndefR.Links.RealDat.chain_of_scalar_update hGiv.core.chain kap lam
      thP := Formalism.IndefR.Links.RealDat.theta_props_of_scalar_update hGiv.core.thP kap lam
      scal := hScal }

  obtain ⟨i, hi⟩ := GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.exists_last D
  have hShare := hx₀ D L hP heps' hxL hSz hTie G Pl0 T A Ks (R.upd6 kap lam) F hSet i hi b
  exact ⟨i, GlobalTheory.IndefiniteRowSideFullHecke.DegreeClassification.GoodShare.ne_bot (R.upd6 kap lam) F hShare⟩

end GlobalTheory.LiftRows

end
end
