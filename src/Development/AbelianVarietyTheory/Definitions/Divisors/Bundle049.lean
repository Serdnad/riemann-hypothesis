module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
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

@[expose] public section

section

open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct Classical

namespace GlobalTheory.AdTh.CcModel

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem realM_mt {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (h : GA D W) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (hth : IsInfEmb τ th) :
    realM θ (Formalism.L2.Theta.mt W h) τ = archM W th h := by
  have e : θ hτ.choose = th :=
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ _ _ (by have := hθ hτ.choose; rwa [← hτ.choose_spec] at this) hth
  rw [realM, dite_eq_left hτ, compAt, e]
  rfl

theorem exists_atComp {θ : InfFam D} (hθ : IsInfFam θ) {W : HSp D} {r : ℕ} (hr : W.rank = r)
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (dict : GA D W → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hΨ : ∀ k, ∀ τ ∈ (U.X k).Ψ, ∃ ρ, τ = tauE D ρ)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hD : DictLat U W hr dict ι e F ik φ th x₀) (h : GA D W) :
    ∃ γ, AtComp θ W hr U.X dict x₀ h γ := by
  obtain ⟨γ, hγ, h1, -, h3⟩ := hD.2 h
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [h1, latR, Submodule.map_coe]
    rfl
  · funext τ
    have := h3 τ
    rw [← realM_mt hθ W (γ * h) τ.1 (hΨ _ _ τ.2) _ (hth _ τ)] at this
    exact this

variable {θ : InfFam D} {V W : HSp D} {r : ℕ} {hr : W.rank = r} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}
    {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r}
    {dict : GA D W → Σ k, Frame (U.X k).Ψ r} {mu : GA D W → ℂ} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f₀ : WO V W → ℂ} {cc cc' : U.Comp → ℂ}

end

end GlobalTheory.AdTh.CcModel
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.Vanishing

namespace GlobalTheory.HSShort

variable {F : Type} [Field F] [NumberField F]

abbrev Tot (G : Geo F) : Type := ∀ j, G.Sec j

def shiftAt (G : Geo F) (u : Fin G.N → F) : ∀ j, Tot G →ₗ[F] G.Sec j
  | 0 => 0
  | j + 1 => G.mulW j u ∘ₗ LinearMap.proj j

def shift (G : Geo F) : (Fin G.N → F) →ₗ[F] Module.End F (Tot G) where
  toFun u := LinearMap.pi (shiftAt G u)
  map_add' u v := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]
  map_smul' c u := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]

def incl (X : Data F) (j : ℕ) : X.V j →ₗ[F] Tot X.toGeo := LinearMap.single F _ j ∘ₗ (X.V j).subtype

theorem incl_injective (X : Data F) (j : ℕ) : Function.Injective (incl X j) := fun a b h =>
  Subtype.ext (by simpa [incl] using congrFun h j)

def inclEquiv (X : Data F) (j : ℕ) : X.V j ≃ₗ[F] LinearMap.range (incl X j) := LinearEquiv.ofInjective _ (incl_injective X j)

def sysOf (X : Data F) (Λ₀ : ℝ) : Sys F (Tot X.toGeo) where
  N := X.N
  n := X.n
  D := X.D
  T := X.T
  w := X.w
  fr := X.A
  mul := shift X.toGeo
  V j := LinearMap.range (incl X j)
  M j := (X.M j).map ((inclEquiv X j).toLinearMap.restrictScalars (𝓞 F))
  nm j := comap (X.nm j) (inclEquiv X j).symm.toLinearMap (inclEquiv X j).symm.injective
  beta := X.beta
  abelian₂ := X.abelian₂
  Lam0 := Λ₀
  LamD := X.LamD
  LamT := X.LamT

def totExt (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Tot G →ₛₗ[algebraMap F E] Tot (G.baseChange E) where
  toFun x j := G.toExt E j (x j)
  map_add' x y := funext fun j => map_add _ _ _
  map_smul' c x := funext fun j => map_smulₛₗ (G.toExt E j) c (x j)

section Split

variable {X : Data F} {s : Fin X.D → Fin X.N → F} {hs : X.IsGood s} {δ : ℕ}

def totRes (Co : Coord X.toGeo hs δ) : Tot X.toGeo →ₗ[F] (Fin δ → F) :=
  (Co.ev 0).toLinearMap ∘ₗ hs.res 0 ∘ₗ LinearMap.proj 0


variable (X s) in
def totFil (a : ℕ) : Submodule F (Tot X.toGeo) := (filV X s a).map (incl X X.T)

def totSym (Co : Coord X.toGeo hs δ) (a : ℕ) : totFil X s a →ₗ[F] (MonoDeg (Fin X.D) a × Fin δ → F) :=
  symV Co a ∘ₗ (Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)).symm.toLinearMap

end Split

end GlobalTheory.HSShort
end
end
