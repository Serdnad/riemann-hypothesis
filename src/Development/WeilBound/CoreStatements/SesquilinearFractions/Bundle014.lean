module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle050
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle003
public import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle013
public import Development.WeilBound.CoreStatements.SesquilinearFractions.PerDiscrete
public import Development.WeilBound.CoreStatements.SesquilinearFractions.IntegralLieModel
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
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle011
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle012

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem gram_signature_orthogonal_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La), IsTypeFn H p q ty → p + q = D.p + D.q → LinearIndependent (𝓞 E) x → (∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ((gramE D (x ∘ Sum.inl)).map fun a => Complex.I * τ a).PosDef ∧ (-((gramE D (x ∘ Sum.inr)).map fun a => Complex.I * τ a)).PosDef) → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsPure hP x := by
  intro E _ _ _ H D g ty p q x hty hpq hx horth hpos
  have := D.fin
  have := D.proj
  have hcard : Fintype.card (Fin p ⊕ Fin q) = Module.finrank (𝓞 E) D.La := by
    rw [D.rank, ← hpq]; simp
  obtain ⟨n, hn0, hn⟩ := exists_nsmul_mem_span_full_family x hcard hx
  have hc0 : ∀ y, DPer.coef D x hx n hn y = 0 → y = 0 := DPer.eq_zero_of_coef D x hx n hn hn0
  have hcx := DPer.planeCoef_mulVec_smul_x_eq_zero_of_ne D x hx n hn
  have hP : IsPeriod D ty (DPer.per hty (DPer.coef D x hx n hn) n) := by
    refine ⟨DPer.per_smul hty _ n, ?_, DPer.per_discrete hty _ n hn0 hc0, DPer.per_span hty x _ n hn0 hcx,
      DPer.Hm hty (gramE D x), DPer.Hm_herm hty _ ?_, DPer.Hm_pos hty _ (fun τ h => (hpos τ h).1) (fun τ h => (hpos τ h).2),
      DPer.herm_EF hty _ n hn0 x (DPer.coef_sum D x hx n hn) horth⟩
    · rw [injective_iff_map_eq_zero]
      exact fun y h => hc0 y (DPer.coef_zero_of_per hty _ n hn0 y h)
    · exact fun m m' => (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 (x m) (x m')
  refine ⟨_, hP, fun a => ?_, fun b => ?_⟩
  · intro k hk
    exact DPer.per_inl hty _ n _ a (hcx _) k (by simpa [sgnRt] using hk)
  · intro k hk
    exact DPer.per_inr hty _ n _ b (hcx _) k (by simpa [sgnRt] using hk)

end PositivityTheory.Xgf
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

def ImageIff (X : CMPack Z c FU i hP) : Prop := ∀ b a u, X.IsImage b a u ↔ u = (Mm X).pt (lam X b a)

def LamSmul (X : CMPack Z c FU i hP) : Prop := ∀ b (s : 𝓞 E) a, lam X b (s • a) = ρm X s (lam X b a)

def LamAdd (X : CMPack Z c FU i hP) : Prop := ∀ b a a', lam X b (a + a') = lam X b a + lam X b a'

def LamRt (X : CMPack Z c FU i hP) : Prop :=
  ∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρm X H.rt (lam X b a) = s • lam X b a

def CMVecIff (X : CMPack Z c FU i hP) : Prop :=
  ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = (Mm X).pt (HT.eigProj (ρm X) (X.β.comp (tauE c τ)) (lam X b a))

end PositivityTheory.Xgf.cm_lie_model_action

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.cm_lie_model_action in
theorem cm_pack_lie_properties (h : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP),
      ImageIff X ∧ LamSmul X ∧ LamAdd X ∧ LamRt X ∧ CMVecIff X) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X
  obtain ⟨h1, h2, h3, h4, h5⟩ := h E H D l Xo c g ty FU i Z P hP X
  exact ⟨Mm X, ρm X, lam X, hρm X, h1, h2, h3, h4, h5⟩

end PositivityTheory.Xgf

end
end
