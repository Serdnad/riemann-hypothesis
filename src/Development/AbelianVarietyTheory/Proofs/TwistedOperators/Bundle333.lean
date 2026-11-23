module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle006
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle317
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareAgree

variable {D : D7}

theorem kapX_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := by
  have k : (Formalism.L2.Theta.mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (Formalism.L2.Theta.mt X g).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ) := rfl
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, ← Matrix.submatrix_map]
  rw [k]

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g), by
    show (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) = _
    exact kapX_mem X e hJ g⟩

theorem mat_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) = reindex e e (Formalism.L2.Theta.mt X g) := rfl

section Datum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

def IsDatum (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ) : Prop :=
  Φ ∈ GlobalTheory.WeilM.schA F _ ∧ ∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = f (crd u)

def algD (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧
    Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}

theorem rho_zero (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ 0 Φ = Φ := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end Datum

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

structure IsOver (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
    (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) : Prop where

  psi : Bs.ψ = ψ

  alpha : Xc.α = α

  beta : Xc.β = β

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ

  measW : Γ.M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW)

  domW : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW '' 𝓕

  measW₁ : Γ.M'.μ = ν₁.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁)

  domW₁ : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ '' 𝓕₁

  weilA : ∀ Φ f, IsDatum Γ.M ψ cA Φ f → ∀ g h,
    IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW g, kapX X e JX h) Φ) (ωA (g, h) f)

  weilB : ∀ Φ f, IsDatum Γ.M' ψ cB Φ f → ∀ g h,
    IsDatum Γ.M' ψ cB (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ g, kapX X e JX h) Φ) (ωB (g, h) f)

  algA : ∀ Φ ∈ algF ψ θ true A B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ

  algA' : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA ΦD Φ

  algB : ∀ Φ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB ΦD Φ

  algB' : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΦD Φ

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem IsOver.theta_eq_A (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA Φ f) (g : GA D W) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g) (kapX X e hO.JX h) = thetaKO ωA g h f := by
  have := (hO.weilA Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

theorem IsOver.theta_eq_B (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W₁ X → ℂ}
    (hD : IsDatum Γ.M' ψ cB Φ f) (g : GA D W₁) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ g) (kapX X e hO.JX h) = thetaKO ωB g h f := by
  have := (hO.weilB Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

end GlobalTheory.SquareAgree

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilDetermined

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ H.std S T (om' p⁻¹ * om p)
    (fun f hf => H'.om_pres _ _ (H.om_pres _ _ hf))
    (fun w f hf => by
      obtain ⟨g, h⟩ := p
      have e := GlobalTheory.AdelicLatMove.actO_actO_inv S T g⁻¹ h⁻¹ w
      rw [inv_inv, inv_inv] at e
      rw [Module.End.mul_apply, Module.End.mul_apply, H.om_heis g h w f hf, Prod.inv_mk,
        H'.om_heis _ _ _ _ (H.om_pres _ _ hf), e])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, H'.om_unit μ 𝓕 hμ h𝓕 _ _ (H.om_pres _ _ hf), H.om_unit μ 𝓕 hμ h𝓕 _ _ hf])
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, fun f hf => ?_⟩
  have := congrArg (om' p) (h f hf)
  rwa [Module.End.mul_apply, om_om_inv, map_smul] at this

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  refine ⟨heisO ψ S T w f, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w, ?_⟩
  unfold heisO
  rw [zero_add]
  refine mul_ne_zero ?_ hw
  exact (ψ.val_isUnit _).ne_zero

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 := by
  intro i j
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self, Matrix.zero_apply, mul_zero]

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 := by
  obtain ⟨x, hx⟩ := exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := exists_isDetAt he.1 T h
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [hc f hf, map_smul, h2 ℓ hℓ f hf, smul_eq_mul] at e1
  have e2 : (c : ℂ) * r' = r := by
    apply mul_right_cancel₀ (mul_ne_zero (Circle.coe_ne_zero (splitFacO χS χT x y)) hne)
    linear_combination e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  apply mul_right_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne')
  rw [e2, Circle.coe_one, one_mul]

theorem agree_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f := by
  intro D ψ hψ S T χS χT om om' H H' p f hf
  by_cases h0 : f = 0
  · rw [h0, map_zero, map_zero]
  obtain ⟨f₀, hf₀, h00⟩ := exists_ne_zero_at_zero hψ hf h0
  have hne : ∀ q, om' q f₀ ≠ 0 := fun q hq => by
    have := om_inv_om om' q f₀
    rw [hq, map_zero] at this
    exact h00 (by rw [← this]; rfl)
  choose c hc using exists_scalar H H'
  have hmul : ∀ q q', c (q * q') = c q * c q' := fun q q' => by
    apply Circle.ext
    apply smul_left_injective ℂ (hne (q * q'))
    have := hc (q * q') f₀ hf₀
    dsimp only
    rw [← this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc q' f₀ hf₀, map_smul,
      hc q _ (H'.om_pres _ _ hf₀), smul_smul, Circle.coe_mul, mul_comm]
  have hcont : Continuous c := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun q => ?_)
    obtain ⟨w, hw⟩ := Function.ne_iff.1 (hne q)
    have h1 : ContinuousAt (fun q' => om q' f₀ w / om' q' f₀ w) q :=
      (H.om_cont f₀ hf₀ w).continuousAt.div (H'.om_cont f₀ hf₀ w).continuousAt hw
    refine h1.congr ?_
    filter_upwards [(H'.om_cont f₀ hf₀ w).continuousAt.eventually_ne hw] with q' hq'
    rw [hc q' f₀ hf₀, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hq']
    rfl
  have hrat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, c (γ, γ') = 1 := fun γ hγ γ' hγ' => by
    have h1 := congrFun (hc (γ, γ') f₀ hf₀) 0
    rw [Pi.smul_apply, H.om_aut γ hγ γ' hγ' f₀ hf₀, H'.om_aut γ hγ γ' hγ' f₀ hf₀, smul_eq_mul] at h1
    apply Circle.ext
    apply mul_right_cancel₀ h00
    rw [← h1, Circle.coe_one, one_mul]
  let ν : GA D S × GA D T →* Circle := MonoidHom.mk' c hmul
  have hS := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S (ν.comp (MonoidHom.inl _ _)) (hcont.comp (Continuous.prodMk_left _))
    (fun γ hγ => hrat γ hγ 1 (one_mem _))
    (fun e he g hg => scalar_split H H' he hg (suppAt_one e T) (hc (g, 1)))
  have hT := GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D T (ν.comp (MonoidHom.inr _ _)) (hcont.comp (Continuous.prodMk_right _))
    (fun γ hγ => hrat 1 (one_mem _) γ hγ)
    (fun e he h hh => scalar_split H H' he (suppAt_one e S) hh (hc (1, h)))
  have h1 : c p = 1 := by
    have e : p = (p.1, 1) * (1, p.2) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
    rw [e, hmul, show c (p.1, 1) = 1 from hS p.1, show c (1, p.2) = 1 from hT p.2, mul_one]
  rw [hc p f hf, h1, Circle.coe_one, one_smul]

theorem hecke_of_mul {χ ξ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D (χ * ξ)) :
    IsHeckeChar D ξ := by
  have := GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h
  rwa [inv_mul_cancel_left] at this

theorem exists_isTildeDet (V : HSp D) {ξ : (AE D)ˣ →* Circle} (hξ : IsHeckeChar D ξ)
    (h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D ξ) (g : GA D V) :
    ∃ x, IsDetRoot V g x ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V ξ g (ξ x) := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V ξ hξ h0
  obtain ⟨x, hx⟩ := aval.1 g
  refine ⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩
  rw [← aval.2 g x hx, ← aval.2 g y hy]

theorem weilDatumTwist (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumTwist D := by
  intro ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h
  have hξ := hecke_of_mul H.hecS H'.hecS
  have hξ' := hecke_of_mul H.hecT H'.hecT
  obtain ⟨om'', H'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ'
    ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩
  obtain ⟨x, hx, ha⟩ := exists_isTildeDet S hξ' h0' g
  obtain ⟨y, hy, hb⟩ := exists_isTildeDet T hξ h0 h
  refine ⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩
  rw [agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]

theorem weilDatumDetermined (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumDetermined D :=
  ⟨(weilDatumTwist D).unique, weilDatumTwist D⟩

end GlobalTheory.WeilDetermined
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumFockLaws

theorem vacuumFock_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D :=
  fun D => vacuumFock_of_thetaSquareIntegrable D (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D)

end GlobalTheory.VacuumFockLaws
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links

namespace GlobalTheory.AdIsomObj

theorem adelicIsometries_obj (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.AdelicIsometries D :=
  GlobalTheory.AdIsom.adelicIsometries D

theorem frames_exist (D : D7) (V : HSp D) (N : ℕ) : ∃ β Λ, IsSDFrame V β Λ N :=
  (adelicIsometries_obj D).2.2.2.2.2.2.2.2.2.2.2.1 V N

end GlobalTheory.AdIsomObj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalFactorUnitary

variable {D : D7}

theorem actO_gAt_of_wAt_eq_zero (S T : HSp D) (p : Place D) (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : wAt p u = 0) : actO S T (gAt S p g) (gAt T p h) u = u := by
  obtain ⟨hsplit, hcomm⟩ := (GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).2 S T p g h u
  have hz : idem D p • actO S T g h u = 0 := by
    rw [← wAt_eq_smul, hcomm, hu]
    unfold actO
    simp
  have hrest : (1 - idem D p) • u = u := by
    rw [sub_smul, one_smul, ← wAt_eq_smul, hu, sub_zero]
  rw [hsplit, hz, hrest, zero_add]

theorem compAt_mt_gAt {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (p : Place D) (g : GA D V) (τ : D.what₂.Tau)
    (hτ : Sum.inr τ ≠ p) : compAt θ τ (Formalism.L2.Theta.mt V (gAt V p g)) = 1 := by
  have h0 : (θ τ) ((infPart D) (idem D p)) = 0 := by
    obtain ⟨-, -, -, hfin, -, -, hinf⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
    rcases p with v | τ'
    · rw [(hfin v).1, map_zero]
    · have hne : τ' ≠ τ := fun e => hτ (by subst e; rfl)
      exact (hinf θ hθ τ).2 τ' hne
  unfold compAt
  rw [((GlobalTheory.T.adelicUnitaryComponentAtPlace_laws D).1 V p g).1]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, h0, zero_mul, zero_add, sub_zero, one_mul]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isLocal_om_gAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (p : Place D) (f : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT p f → ∀ g h, IsLocal ψ θ S T sS sT ΛS ΛT p (om (gAt S p g, gAt T p h) f) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT hW hθ p f hf g h
  unfold IsLocal IsLatVac IsFockVacAt at hf ⊢
  obtain ⟨hth, ⟨hdbl, hhalf⟩, hfock⟩ := hf
  have hoff : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      (fun v => Sum.inl v ≠ p), wAt p u = 0 := fun u hu =>
    (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 (fun _ hv => hv)
  refine ⟨hW.om_pres _ f hth, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have hw2 : wAt p (2 • u) = 0 := by
      rw [wAt_eq_smul, smul_comm, ← wAt_eq_smul, hoff u hu, smul_zero]
    have key := hW.om_heis (gAt S p g) (gAt T p h) (2 • u) f hth
    rw [hdbl u hu, actO_gAt_of_wAt_eq_zero S T p g h (2 • u) hw2] at key
    exact key.symm
  · intro e he u hu hu'
    have key := hW.om_heis (gAt S p g) (gAt T p h) u f hth
    rw [hhalf e he u hu hu', actO_gAt_of_wAt_eq_zero S T p g h u (hoff u hu)] at key
    exact key.symm
  · intro τ hτ z
    have hT1 : compAt θ τ (Formalism.L2.Theta.mt T (gAt T p h)) = 1 := compAt_mt_gAt hθ T p h τ hτ
    have hS1 : compAt θ τ (Formalism.L2.Theta.mt S (gAt S p g)⁻¹) = 1 := by
      rw [← gAt_inv]
      exact compAt_mt_gAt hθ S p g⁻¹ τ hτ
    have e1 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ z hth
    have e2 := GlobalTheory.WeilVacMove.om_dRho hW hθ (gAt S p g) (gAt T p h) τ (cplxO (sS τ) (sT τ) z) hth
    rw [hT1, hS1, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have hz := hfock τ hτ z
    unfold annih at hz ⊢
    rw [← e1, ← e2, ← map_smul, ← map_add (f := _), hz, map_zero]

end GlobalTheory.LocalFactorUnitary
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, (∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ y : Mx D a b, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ (GlobalTheory.IsoMean.emb V W P Q y))| ^ m * ‖f y‖ ≤ C) → ∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C := by
  first | exact @GlobalTheory.DecayCoord.decay_real_coords | exact GlobalTheory.DecayCoord.decay_real_coords | (intros; apply GlobalTheory.DecayCoord.decay_real_coords <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KernelSeminorm

theorem thetaGrowth_onObjects : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D :=
  fun D => GlobalTheory.KernelSeminorm.thetaGrowth D

end GlobalTheory.KernelSeminorm
end
