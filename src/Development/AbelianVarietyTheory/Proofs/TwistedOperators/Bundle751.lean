module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle748
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle614
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle750
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle741
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle622
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle749
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle520
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UniBF

private theorem psiE_add_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) :
    psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  simp only [psiE, map_add (f := _), AddChar.map_add_eq_mul]

private theorem psiE_zero_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  simp only [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiUni_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ,
    MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ →
    psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W Mv hM F hF ρ h u hu hx
  have hA := GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional D hq T L μ0 hL sc G W Mv hM F hF ρ h
  have hB := GlobalTheory.T.additive_character_superdiag_trivial D hq T L μ0 hL sc G W Mv hM F hF ρ h
  set N : Mx D ρ ρ := u.1.1 - 1 with hNdef
  have hx' : (F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ∈ latRow G (2 * ρ + 1) := by
    have e : xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) = (F.dJ ρ h).jX ⬝ N := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one]; rfl
    rw [← e]; exact hx
  have hN : (F.dJ ρ h).pX ⬝ ((F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ⬝ (F.dB ρ h).jX) = N := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, ← Matrix.mul_assoc, HypDec.pX_jX,
      Matrix.one_mul]
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have e1 : u.1.1 i j = N i j := by rw [hNdef, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [e1]
    refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (hu i j) fun v _ => ?_
    have ho := GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)
    by_cases hv : v ∈ G.pl.S0
    · have := hB _ hx' i j hij v hv _ ho
      rwa [hN] at this
    · have := hA _ hx' i j hij v hv _ ho
      rwa [hN] at this
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero_one W.ψ

end GlobalTheory.AscFin.UniBF

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


namespace GlobalTheory.LineZero

variable {D : D7}

noncomputable def mulL {k m n : ℕ} (A : Mx D k m) : Mx D m n →+ Mx D k n where
  toFun y := A * y
  map_zero' := Matrix.mul_zero _
  map_add' y y' := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S B T : HSp D} (M : Matrix (Fin T.rank) (Fin B.rank) D.host.E)
    {LS : Set (Fin S.rank → D.host.E)} {LB : Set (Fin B.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hM : ∀ t ∈ LB, M *ᵥ t ∈ LT) {y : WO S B} (hy : y ∈ latO S B LS LB P) :
    (rat M : Mx D T.rank B.rank) * y ∈ latO S T LS LT P := by
  suffices h : latO S B LS LB P ≤ (latO S T LS LT P).comap (mulL (rat M : Mx D T.rank B.rank)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

end GlobalTheory.LineZero

namespace GlobalTheory.LineZero

variable {D : D7}

theorem latO_le_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib,
      TensorProduct.tmul_neg, neg_neg]
  rw [e]
  exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩)

theorem rat_mul_mem_hatMx {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E)
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} {N' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)}
    (hA : ∀ x ∈ N, A * x ∈ N') {y : Mx D m n} (hy : y ∈ hatMx N) : (rat A : Mx D k m) * y ∈ hatMx N' := by
  suffices h : hatMx N ≤ (hatMx N').comap (mulL (rat A : Mx D k m)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, A * x, hA x hx, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.tmul_sum]

theorem mul_mem_smul_homLat {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') (I : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ I • homLat Λ Λ') : A * x ∈ I • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun _ _ hy hy' => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hy z hz)
  · rw [Matrix.mul_add]
    exact add_mem hy hy'

end GlobalTheory.LineZero


open GlobalTheory.LineZero in
theorem GlobalTheory.LineZero.adj_mem_lineLat : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF h u hu
  have h1 := GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO D hq T L μ0 hL sc G W M hM F hF h u hu
  have h2 := GlobalTheory.T.star_adjoint_mem_hat_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  have hz : ∀ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0}, F.oz.iB *ᵥ t ∈ G.Λ (.core 0) := by
    intro t ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [Matrix.mulVec_smul, hF.zB]
    refine Submodule.smul_mem _ c ?_
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, zero_mem _, fun _ => 1, fun _ => FractionalIdeal.one_mem_one _, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  show _ ∈ (latCore G 0).comap _
  rw [AddSubgroup.mem_comap]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    AddMonoidHom.inr_apply]
  rw [GlobalTheory.MixModel.OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB * _)]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_le_negSp (rat_mul_mem_latO F.oz.iB hz h1)
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx F.oz.iB (fun x hx => mul_mem_smul_homLat F.oz.iB hz _ hx) (h2 e he)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobiToBessel_lattice_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  first | exact @GlobalTheory.AscFin.SplitsFB.splits_FB | exact GlobalTheory.AscFin.SplitsFB.splits_FB | (intros; apply GlobalTheory.AscFin.SplitsFB.splits_FB <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.GoodPosBF

theorem goodPosition_offBadPlaces_from_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v ∧ StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v ∧ (0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  refine ⟨⟨sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e), (I.2.1 ρ h).1,
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e),
    sd (.core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j e => by cases e),
    ((I.2.1 ρ h).2.1 v).1, ((I.2.1 ρ h).2.1 v).2,
    GlobalTheory.T.psi_primitive_standardFrames_besselLevel D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.besselLevel_columns_carry_latticeLines_offExceptional D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩,
    GlobalTheory.T.standard_lattice_off_S0 D hq T L μ0 hL sc G W M hM F hF ρ h v hv, GlobalTheory.T.lattice_membership_adjoint_iff D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩

end GlobalTheory.GoodPosBF
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.RungJac

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.om = om ∧ s.χV = χV ∧ s.χW = χW ∧ s.vW = vW := by

  have hdesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨omA, hA⟩ := (hdesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hdesc ψ V₀ W χV χW omA hA).2 W₀ σ dW

  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨{ χV := χV, χW := χW, om := om, om₀ := om₀, weil := h, weil₀ := h₀, vW := vW, vS := vS, vT := vT, vU := vU },
    rfl, rfl, rfl, rfl⟩

private theorem rapidDec_star' {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : RapidDec V f) : RapidDec V (star f) := by
  refine ⟨fun γ hγ g => ?_, continuous_star.comp hf.2.1, fun N => ?_⟩
  · show star (f (γ * g)) = star (f g)
    rw [hf.1 γ hγ g]
  · obtain ⟨C, hC⟩ := hf.2.2 N
    exact ⟨C, fun g => by simpa only [Pi.star_apply, norm_star] using hC g⟩

private theorem isHeckeChar_of_isHeckeChar_mul {D : D7} {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ)
    (h' : IsHeckeChar D (χ * χ')) : IsHeckeChar D χ' := by
  have e : (χ' : (AE D)ˣ → Circle) = fun x => (χ x)⁻¹ * (χ * χ') x := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact h.1.inv.mul h'.1
  · have hx := h'.2 x
    rw [MonoidHom.mul_apply, h.2 x, one_mul] at hx
    exact hx



theorem rungJ : FockTot → PartFixed → RungJ := by
  intro hFock hFix D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h h' hB
  obtain ⟨ρ, Φ, hne⟩ := hB
  have hi : 2 * k + 2 < D.R.m := by omega

  obtain ⟨c1, c2, -, c4, c5, c6, c7, c8, c9h, c9f⟩ :=
    GlobalTheory.T.gridConjugation_weilData_inverseCharacter D hD T L μ0 hL sc G W M hM (2 * k + 2) hi
  obtain ⟨c4a, c4b⟩ := c4 ⟨k + 1, by omega⟩
  rw [c4a, c4b] at c1

  have hex := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hc2 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c2⟩
  have hc1 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c1⟩
  have hEta : IsHeckeChar D L.eta := isHeckeChar_of_isHeckeChar_mul hc2.2.1 hc1.2.2.1
  obtain ⟨omz, hz⟩ : ∃ omz : Om (G.V (.core (2 * k + 2 + 1))) (negSp F.Lz),
      IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta omz := by
    refine hex _ _ W.ψ _ _ W.ψ_std hc2.2.1 hEta hc2.2.2.2.1 ?_
    show ResEta D L.eta F.Lz.rank
    rw [F.rk]
    exact GlobalTheory.HeckeCharacterRestriction.resEta_eta hL

  obtain ⟨s, hs_om, hs_χV, hs_χW, hs_vW⟩ := exists_step (F.dJ (k + 1) h) (F.dB k h') c1
    ⟨M.ν (.grid (2 * k + 2) 0), M.fd (.grid (2 * k + 2) 0), c9h, c9f⟩
  obtain ⟨𝒮, Γ₀, hLoc, hRow, hBox⟩ := hGood.fb k h h' s hs_om

  obtain ⟨f, hf, hΨi⟩ := hΨ.2 (2 * k + 2) hi
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hGood.lineNe (k + 1) h
  have hVf := (c5 f).1 hf
  have hRφ : RapidDec _ (star (Ψ (2 * k + 2 + 1))) := rapidDec_star' (hΨ.1 _ (by omega))
  have hRG : RapidDec _ (star (part W M ρ Φ u (2 * k + 2) h')) := rapidDec_star' (hu ρ Φ _ _)
  have hK : ∀ x ∈ lev G (.grid (2 * k + 2) 0), ∀ g,
      star (part W M ρ Φ u (2 * k + 2) h') (g * x) = star (part W M ρ Φ u (2 * k + 2) h') g :=
    fun x hx g => congrArg star (hFix D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k + 1) h' x hx g)

  have hper : (F.bes v k h').per W.ψ
      (liftT (omCore W (2 * k + 2)) (v (2 * k + 2 + 1)).μ (v (2 * k + 2 + 1)).𝓕 (star (Ψ (2 * k + 2 + 1))) (star f))
      (star (part W M ρ Φ u (2 * k + 2) h')) ≠ 0 := by
    rw [← c6 v f (Ψ (2 * k + 2 + 1)), ← hΨi]
    exact hne

  obtain ⟨Φ', hΦ'𝒮, hΦ'ne⟩ := GlobalTheory.T.bessel_period_gives_fourierJacobi_period_of_lift D W.ψ k (F.jac v (k + 1) h) (F.bes v k h') s 𝒮 Γ₀ _ hLoc
    (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta (omCore W (2 * k + 2)) omz hs_χW (by rw [hs_χV]; exact c2)
    (by rw [hs_χV]; exact hz) _ _ hRφ hRG hK (star f) Φ₀ hVf.1 hΦ₀.1 hΦ₀ne (hBox _ _ hVf hΦ₀) hper

  have hTame := (GlobalTheory.T.thetaLift_periods_isTameThetaFunctional D W.ψ _ s.vW (star (part W M ρ Φ u (2 * k + 2) h')) hRG).2 (k + 1)
    (F.jac v (k + 1) h) _ _ s.om s.weil (negSp F.Lz) (F.ζ (k + 1)) _ _ omz hz (star (Ψ (2 * k + 2 + 1))) Φ₀ hRφ hΦ₀.1
  have hFk := hFock D hD T L μ0 hL sc G W M hM ⟨2 * k + 2, hi⟩ _ hTame
  obtain ⟨κ, P, hκP⟩ : ∃ κ P, (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (s.lift (star (part W M ρ Φ u (2 * k + 2) h')) (star (W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P))) Φ₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hΦ'ne (hFk hall Φ' (hRow Φ' hΦ'𝒮))

  have hpart : part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2) hi.le =
      part W M ρ Φ u (2 * k + 2) hi.le := by
    refine (c8 ρ Φ _ _ u fun j hj => ?_).symm
    have hj' : j ≠ ⟨2 * k + 2, hi⟩ := fun e => by
      rw [e] at hj
      exact lt_irrefl _ hj
    exact ⟨(Function.update_of_ne hj' P ρ).symm, (Function.update_of_ne hj' κ Φ).symm⟩
  have hdat : W.datum (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) ⟨2 * k + 2, hi⟩ =
      W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P := by
    simp only [GridData.Weil.datum, Function.update_self]
  have hlift := c7 (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u
  rw [hpart, hdat] at hlift
  have e2 : ∀ G0 X, s.lift G0 X = liftS (omRow W (2 * k + 2)) (M.ν (.grid (2 * k + 2) 0)) (M.fd (.grid (2 * k + 2) 0)) G0 X := by
    intro G0 X
    show liftS s.om s.vW.μ s.vW.𝓕 G0 X = _
    rw [hs_om, hs_vW]
  rw [e2] at hκP
  refine ⟨_, omz, hz, Function.update ρ ⟨2 * k + 2, hi⟩ P, Function.update Φ ⟨2 * k + 2, hi⟩ κ, Φ₀, hΦ₀, ?_⟩
  have key : (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (star (part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2 + 1) hi)) Φ₀ ≠ 0 := by
    rw [hlift]
    exact hκP
  exact key

end GlobalTheory.Asc.RungJac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem pairPts_update_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc hU hβ hτ hv Ψ F x y i hi him k hk
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hF : Function.update y (j + 1) (y (j + 1) * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [hF, pairPts_eq_sum, pairPts_eq_sum]
  have hth : ∀ d ∈ τ.support, ∀ a, vecOf S d a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    cases a with
    | inl j' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .top t j') (by show (j' : ℕ) + 1 ≤ D.R.m; omega) _ ((hv d hd).1 j')
    | inr i' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .chi i' D.R.m) ⟨by omega, rfl⟩ _ ((hv d hd).2 i')
  have e1 : (τ.sum fun d c => c • pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) (vecOf S d)) =
      τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d)) :=
    Finsupp.sum_congr fun d hd => by rw [GlobalTheory.RowVertexInv.pairFn_update_moveV S x y j him k _ (hth d hd)]
  rw [e1]
  have hmv : ∀ d ∈ τ.support, ∀ a, moveV S j him k (vecOf S d) a ∈
      thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    have h1 : (Pair.chi j D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have h2 : (Pair.chi (j + 1) D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have upd : ∀ (P : ∀ a, FactorFn G t a → Prop) (f : ∀ a, FactorFn G t a) (a' : Fin D.R.m ⊕ Fin D.R.m) (v' : FactorFn G t a'),
        (∀ a, P a (f a)) → P a' v' → ∀ a, P a (Function.update f a' v' a) := by
      intro P f a' v' hf hv' a
      by_cases h : a = a'
      · subst h; simpa using hv'
      · rw [Function.update_of_ne h]; exact hf a
    exact upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _
      (upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _ (hth d hd)
        ((W.om_is _ h1).om_pres _ _ (hth d hd (.inr ⟨j, by omega⟩))))
      ((W.om_is _ h2).om_pres _ _ (hth d hd (.inr ⟨j + 1, him⟩))) a
  let V := fun a : Fin D.R.m ⊕ Fin D.R.m => thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))
  let M : MultilinearMap (RingHom.id ℂ) (fun a => ↥(V a)) (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ) :=
    MultilinearMap.mk' (fun v => pairFn S x y fun a => (v a : FactorFn G t a))
      (fun v a f g => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_add]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f g f.2 g.2).1)
      (fun v a c f => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_smul]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f f f.2 f.2).2 c)
  classical
  let φ : PureDat G t → ∀ a, V a := fun d =>
    if hd : d ∈ τ.support then fun a => ⟨moveV S j him k (vecOf S d) a, hmv d hd a⟩ else 0
  let φ' : PureDat G t → ∀ a, V a := fun d => if hd : d ∈ τ.support then fun a => ⟨vecOf S d a, hth d hd a⟩ else 0
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V M τ τ φ φ' (fun z => by
    refine (Finsupp.sum_congr fun d hd => ?_).trans ((GlobalTheory.T.expansionTensorSum_invariant_gridRowLevel S hL hq hc hU hβ hτ hv j him k hk z).trans (Finsupp.sum_congr fun d hd => ?_))
    · simp only [φ, dif_pos hd]
    · simp only [φ', dif_pos hd])
  have l1 : (τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d))) = τ.sum fun d c => c • M (φ d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ, dif_pos hd, MultilinearMap.mk'_apply]
  have l2 : (τ.sum fun d c => c • pairFn S x y (vecOf S d)) = τ.sum fun d c => c • M (φ' d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ', dif_pos hd, MultilinearMap.mk'_apply]
  rw [l1, l2, key]

end GlobalTheory.RowVertexInv
end
