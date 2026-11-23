module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeanRealTorusNormalisedThetaMulConj
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle050
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  first | exact @GlobalTheory.SW.siegel_weil_definite | exact GlobalTheory.SW.siegel_weil_definite | (intros; apply GlobalTheory.SW.siegel_weil_definite <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.mean_realTorus_normalisedTheta_mul_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ Fd : Set (WR X n), IsAddFundamentalDomain (latR X n N) Fd volume → ∀ a b : WR X n, ((volume Fd).toReal : ℂ)⁻¹ * ∫ w in Fd, cexp (π * I * (EFR X w (a - b) : ℝ)) * (thR X bas idx φ₁ x₁ (w + a) * conj (thR X bas idx φ₂ x₂ (w + b))) = dbl X bas idx φ₁ φ₂ 0 * (gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))) := by
  first | exact @GlobalTheory.Ker.Mean.mean_thR_mul_conj | exact GlobalTheory.Ker.Mean.mean_thR_mul_conj | (intros; apply GlobalTheory.Ker.Mean.mean_thR_mul_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem th_bij_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → (∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsZak (C.xB B) φ (C.Th (C.xB B) φ) ∧ C.IsFock B (C.Th (C.xB B) φ)) ∧ (∀ f, C.IsTh f → C.IsFock B f → ∃! φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ) := by
  intro D S T C B hB
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  refine ⟨fun φ hφ => ⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1, ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ).1⟩, ?_⟩
  intro f hf hF
  obtain ⟨φ, hφ, rfl⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C B hB f hf hF
  refine ⟨φ, ⟨hφ, rfl⟩, ?_⟩
  rintro ψ ⟨hψ, h⟩
  exact (((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx φ hφ).1 ψ hψ).2 h).symm

end GlobalTheory.Ker
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem epsW_neg_rows {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (X : Data E r) (w : E)
    (y : Matrix (Fin n) (Fin r) E) : SW.epsW X w (-y) = SW.epsW X w y := by
  have key : ∀ k, EF X ((-y) k) (w • (-y) k) = EF X (y k) (w • y k) := by
    intro k
    change (SW.EFBil X) (-(y k)) (w • -(y k)) = (SW.EFBil X) (y k) (w • y k)
    rw [smul_neg]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  unfold SW.epsW
  rw [Finset.sum_congr rfl (fun k _ => key k)]

theorem latVac_th_iff (D : D7) (S T : HSp D) (C : Ctx S T) (w : D.host.E) (hw : IsIntegral ℤ w)
    (h1 : w + cc w = 1) (h2 : IdemTwo w) (M : ℕ) (Λ : Lt D.host.E S.rank) (hΛ : Λ ∈ Vset D.host.E S.rank M)
    (L : Lt D.host.E T.rank) (hL : SelfD C.X L) (x : Frame C.X.Ψ T.rank) (hx : x ∈ C.X.dom)
    (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔
      ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ := by
  have hth : C.IsTh (C.Th x φ) := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C x hx φ hφ).1.1
  rw [GlobalTheory.T.isLatticeVacuum_iff_signedRational_fixed D S T C w hw h1 h2 M Λ hΛ L hL _ hth]
  have hsb : ∀ y, SW.IsSB (heisG C.X C.bas y φ) := fun y =>
    ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  have hrho := (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx φ hφ).2.2.1
  constructor
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [hrho, neg_neg, epsW_neg_rows] at h'
    have hsb' : SW.IsSB (SW.epsW C.X w y • heisG C.X C.bas y φ) :=
      GlobalTheory.SW.TensVac.rho_sb (idx := C.idx) (hs := C.sympl) (hn := C.even) y hφ
    rw [← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (hsb y)).2.1] at h'
    exact ((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ hsb').1 φ hφ).2 h'
  · intro h y hy
    have h' := h (-y) (neg_mem hy)
    rw [epsW_neg_rows] at h'
    rw [hrho, ← (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C x hx _ (hsb (-y))).2.1, h']

theorem latVac_th_line : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → (∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔ ∀ y ∈ tens Λ L, SW.epsW C.X w y • heisG C.X C.bas y φ = φ)) ∧ ∀ B, C.IsB B → ∀ v, IsVac C.X C.bas w (tens Λ L) v → ∀ f, C.IsTh f → C.IsFock B f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → ∃ t : ℂ, f = t • (C.Th (C.xB B) v) := by
  intro D S T C w hw h1 h2 M Λ hΛ L hL
  refine ⟨fun x hx φ hφ => latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL x hx φ hφ, ?_⟩
  intro B hB v hv f hf hF hlat
  obtain ⟨φ, hφ, rfl⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C B hB f hf hF
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hfix := (latVac_th_iff D S T C w hw h1 h2 M Λ hΛ L hL (C.xB B) hx φ hφ).1 hlat
  have hline := (GlobalTheory.SW.TensVac.vacua D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even
    w hw h1 L hL M Λ hΛ).2.1 v φ hv hφ hfix
  refine ⟨SW.ip φ v, ?_⟩
  calc C.Th (C.xB B) φ = C.Th (C.xB B) (SW.ip φ v • v) := by rw [← hline]
    _ = SW.ip φ v • C.Th (C.xB B) v := (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx v hv.1).2.1 _

end GlobalTheory.Ker
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ctx_base : ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧
    C.q0 = q ∧ S.SigOK ∧ T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
      IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f := by
  intro D n p q
  obtain ⟨S, T, C, h1, h2, h3, h4, h5, B, hB⟩ := exists_ctx_sig D n p q
  obtain ⟨⟨Lv, hw⟩, h6, -⟩ := GlobalTheory.Ker.Base.level_base_fam D S T C
  obtain ⟨f, hf⟩ := h6 Lv B hB
  exact ⟨S, T, C, h1, h2, h3, h4, h5, Lv, B, f, hw, hB, hf⟩

theorem inhabitants :
    (∀ (D : D7) (S T : HSp D) (p q : ℕ) (L : Lt D.host.E T.rank), S.gram = 1 → Even S.rank → p + q = T.rank →
      T.SigOK → (∀ τ, T.sig (tauE D τ) = (p, q)) → IsSelfDualC T L →
      ∃ C : Ctx S T, C.X.p0 = p ∧ C.q0 = q ∧ IsAA C.X.Λ L ∧ ∃ B : C.Bas, C.IsB B) ∧
    ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧ C.q0 = q ∧ S.SigOK ∧
      T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
        IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f :=
  ⟨exists_ctx, exists_ctx_base⟩

end GlobalTheory.Ker.Inhab

end
end
