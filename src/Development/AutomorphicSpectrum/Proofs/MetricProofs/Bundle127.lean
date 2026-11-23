module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle056
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle060
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XFlArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle116
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.WeilBound.CoreStatements.RationalSupMetrics.PullRatiosAlgebraic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle009
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.FlagBun

section Map

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem isFrameAt_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) : (L.map f).IsFrameAt (fun a => f (b a)) p := by
  refine ⟨h.1.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  show (L p).map (f.restrictScalars (regAt ξ p)) = _
  rw [h.2, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isVB_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVB r V) : (L.map f).IsVB r (V.map f) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  refine ⟨U, hU, fun a => f (b a), ?_, fun q hqT hqU => isFrameAt_map_of_injective hf (hq q hqT hqU)⟩
  rw [← hb, Submodule.map_span, ← Set.range_comp]
  rfl

end Map

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

theorem inW_injective (A : HodgeCpt Y S x) : Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective (A : HodgeCpt Y S x) (τ : CMType H) : Function.Injective (inO A τ) := by
  intro a b h
  have e := congrFun (congrArg Prod.snd h) τ
  simpa [inO] using e

end Bundles

theorem LL_isVB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)
    (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 s
  rcases s with τ | τ
  · exact isVB_map_of_injective (inW_injective 𝔐) (𝔐.vb (.inl τ))
  · exact isVB_map_of_injective (inO_injective 𝔐 τ) (omBundle_isVB 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section GenU

variable (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S)

theorem genU_self (a : Fin (r s)) : genU Ω r s a a = 1 := by
  simp [genU]

theorem genU_of_lt {a b : Fin (r s)} (h : a < b) : genU Ω r s a b = 0 := by
  simp [genU, not_lt.2 h.le, h.ne]

theorem genU_of_gt {l k : Fin (r s)} (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) :=
  dif_pos h

end GenU

variable {Ψ : Type} {p q : ℕ} (Ω : Type) [Field Ω]

theorem symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
  rw [← blockEquiv_inl, Equiv.symm_apply_apply]

theorem symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
  rw [← blockEquiv_inr, Equiv.symm_apply_apply]

theorem gMat_apply (τ : Ψ) (i j : Fin (p + q)) :
    gMat p q Ω τ i j = (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ) : Matrix (Fin q) (Fin q) _) 0 0
      (genU Ω (rk Ψ p q) (.inl τ) : Matrix (Fin p) (Fin p) _)) ((blockEquiv p q).symm i) ((blockEquiv p q).symm j) :=
  rfl

theorem gMat_om (τ : Ψ) (a b : Fin q) :
    gMat p q Ω τ (omEmb p q a) (omEmb p q b) = genU Ω (rk Ψ p q) (.inr τ) a b := by
  rw [gMat_apply, symm_omEmb, symm_omEmb]
  rfl

theorem gMat_w (τ : Ψ) (a b : Fin p) :
    gMat p q Ω τ (wEmb p q a) (wEmb p q b) = genU Ω (rk Ψ p q) (.inl τ) a b := by
  rw [gMat_apply, symm_wEmb, symm_wEmb]
  rfl

theorem gMat_om_w (τ : Ψ) (a : Fin q) (b : Fin p) : gMat p q Ω τ (omEmb p q a) (wEmb p q b) = 0 := by
  rw [gMat_apply, symm_omEmb, symm_wEmb]
  rfl

theorem gMat_lowerUni (τ : Ψ) : IsLowerUni (gMat p q Ω τ) := by
  constructor
  · intro a
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    rcases x with x | x
    · rw [blockEquiv_inl, gMat_om]
      exact genU_self Ω (rk Ψ p q) (.inr τ) x
    · rw [blockEquiv_inr, gMat_w]
      exact genU_self Ω (rk Ψ p q) (.inl τ) x
  · intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    rcases x with x | x <;> rcases y with y | y
    · rw [blockEquiv_inl, blockEquiv_inl] at hab ⊢
      rw [gMat_om]
      exact genU_of_lt Ω (rk Ψ p q) (.inr τ) ((omEmb_strictMono p q).lt_iff_lt.1 hab)
    · rw [blockEquiv_inl, blockEquiv_inr, gMat_om_w]
    · rw [blockEquiv_inr, blockEquiv_inl] at hab
      have h : q + (x : ℕ) < (y : ℕ) := hab
      have := y.2
      omega
    · rw [blockEquiv_inr, blockEquiv_inr] at hab ⊢
      rw [gMat_w]
      exact genU_of_lt Ω (rk Ψ p q) (.inl τ) ((wEmb_strictMono p q).lt_iff_lt.1 hab)

def loc (t : GenIx (rk Ψ p q)) : Ψ × Fin (p + q) × Fin (p + q) :=
  match t with
  | ⟨.inl τ, lk⟩ => (τ, wEmb p q lk.1.1, wEmb p q lk.1.2)
  | ⟨.inr τ, lk⟩ => (τ, omEmb p q lk.1.1, omEmb p q lk.1.2)

theorem exists_var (x : LowIdx Ψ (p + q) p) :
    ∃ t : GenIx (rk Ψ p q), loc t = x.1 ∧ gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 =
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) := by
  obtain ⟨⟨τ, a, b⟩, hlt, hiff⟩ := x
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rcases a with a | a <;> rcases b with b | b
  · simp only [blockEquiv_inl] at hlt hiff ⊢
    have h : b < a := (omEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inr τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_om]; exact genU_of_gt Ω (rk Ψ p q) (.inr τ) h⟩
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hlt
    have h : q + (b : ℕ) < (a : ℕ) := hlt
    have := a.2
    omega
  · exfalso
    simp only [blockEquiv_inl, blockEquiv_inr] at hiff
    have h : (q + (a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p) := hiff
    have := b.2
    omega
  · simp only [blockEquiv_inr] at hlt hiff ⊢
    have h : b < a := (wEmb_strictMono p q).lt_iff_lt.1 hlt
    exact ⟨⟨.inl τ, ⟨(a, b), h⟩⟩, rfl, by
      rw [gMat_w]; exact genU_of_gt Ω (rk Ψ p q) (.inl τ) h⟩

theorem gMat_indep :
    AlgebraicIndependent Ω fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2 := by
  choose e he₁ he₂ using exists_var (Ψ := Ψ) (p := p) (q := q) Ω
  have hinj : Function.Injective e := fun x y h => Subtype.ext (by rw [← he₁ x, ← he₁ y, h])
  have hX : AlgebraicIndependent Ω fun t : GenIx (rk Ψ p q) =>
      algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t) :=
    (MvPolynomial.algebraicIndependent_X (GenIx (rk Ψ p q)) Ω).map'
      (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)))
      (IsFractionRing.injective _ _)
  have e' : (fun x : LowIdx Ψ (p + q) p => gMat p q Ω x.1.1 x.1.2.1 x.1.2.2) =
      (fun t : GenIx (rk Ψ p q) =>
        algebraMap (MvPolynomial (GenIx (rk Ψ p q)) Ω) (GenField Ω (rk Ψ p q)) (MvPolynomial.X t)) ∘ e :=
    funext he₂
  rw [e']
  exact hX.comp e hinj

theorem gMat_isGenericFlag : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω],
    GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := fun _ _ _ _ Ω _ =>
  IsGenericFlag.of_lowerUni (fun τ => gMat_lowerUni Ω τ) (gMat_indep Ω)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem basis_image {Ω M N ι : Type} [Field Ω] [AddCommGroup M] [Module Ω M] [AddCommGroup N] [Module Ω N]
    (b : Module.Basis ι Ω M) (f : M →ₗ[Ω] N) (hf : Function.Injective f) :
    LinearIndependent Ω (fun a => f (b a)) ∧
      Submodule.span Ω (Set.range fun a => f (b a)) = (⊤ : Submodule Ω M).map f := by
  refine ⟨b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  have h : (Set.range fun a => f (b a)) = f '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, b.span_eq]

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  unfold inO
  rw [LinearMap.coe_comp]
  refine LinearMap.inr_injective.comp ?_
  rw [LinearMap.coe_single]
  exact Pi.single_injective τ

theorem cc_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO s
  rcases s with τ | τ
  · have h := basis_image (bW τ) ((inW 𝔐).comp (𝔐.Vgen (.inl τ)).subtype)
      ((inW_injective 𝔐).comp Subtype.val_injective)
    rw [Submodule.map_comp, Submodule.map_subtype_top] at h
    exact h
  · exact basis_image (bO τ) (inO 𝔐 τ) (inO_injective 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def segIxEquiv : ((k : K₀ ⊕ StepIx Ψ p q) → idx (p := p) (q := q) J₀ n k) ≃
    FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q) :=
  Equiv.sumPiEquivProdPi (idx (p := p) (q := q) J₀ n)

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  classical
  obtain ⟨hL, hc, hφ, hB⟩ := hF
  set r := rk (CMType H) D.p D.q with hr
  set x : ((k : K₀) → J₀ k) → Ω := seg x₀ with hxdef
  set cF := cc 𝔐 bW bO with hcF
  have hx : CoordTie ℤ 𝔐.ξ x := 𝔐.tie
  obtain ⟨c₀, hc₀⟩ := hx.cover ⟨genPt 𝔐.ξ, specializes_refl _⟩
  have hB' : ∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (cF s l)) = 1 := hB
  obtain ⟨J₁, hJ₁, hfrac⟩ := GlobalTheory.T.frame_matrix_chart_ratios Ω (EE 𝔐) (CMType H ⊕ CMType H) r n ((k : K₀) → J₀ k) x φ cF c₀ hc₀.1
    (GlobalTheory.T.function_field_ratio_generators 𝔐.X Ω 𝔐.ξ _ x c₀ hx hc₀.1) hB'
  have : Finite (FlagIx ((k : K₀) → J₀ k) n r) := by unfold FlagIx; infer_instance
  obtain ⟨X', ξ', s', hx', hirr', -, hprop, -⟩ :=
    GlobalTheory.T.exists_proper_integral_model (GenField Ω r) ℤ (FlagIx ((k : K₀) → J₀ k) n r) (flagCoord _ x φ cF) J₁ hJ₁ hfrac
  obtain ⟨f, hdom, hch⟩ := GlobalTheory.T.dominates_of_coords_regular 𝔐.X Ω 𝔐.ξ ℤ _ x X' (GenField Ω r) ξ' (algebraMap Ω (GenField Ω r)) hx hx'.gen
    hirr' (fun z p' => by simp [intCast_mem (regAt ξ' p') z]) (fun p' => by
      obtain ⟨⟨c1, J⟩, hne, hrat⟩ := hx'.cover p'
      have e1 : ∀ k, flagCoord _ x φ cF (k, J) = algebraMap Ω (GenField Ω r) (x k) *
          ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (J q) (Fin.castLE q.2.2)).det := fun k => rfl
      rw [e1] at hne
      refine ⟨c1, left_ne_zero_of_mul hne, fun k => ?_⟩
      have := hrat (k, J)
      rwa [e1, e1, mul_div_mul_right _ _ (right_ne_zero_of_mul hne)] at this)
  have hsm := GlobalTheory.T.flag_frames_generic_model_right 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ x (CMType H ⊕ CMType H) r (VV 𝔐) (LL 𝔐) m n φ cF X' ξ' f hx 𝔐.all hL hφ hc
    hx' hirr' hdom hch
  have hseg : seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) =
      flagCoord ((k : K₀) → J₀ k) x φ cF ∘ segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀) := by
    funext c'
    show ∏ k, yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨k, c' k⟩ =
      algebraMap Ω (GenField Ω r) (∏ k, x₀ ⟨k, c' (.inl k)⟩) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ cF q.1).submatrix (c' (.inr q)) (Fin.castLE q.2.2)).det
    rw [Fintype.prod_sum_type, map_prod]
    rfl
  refine ⟨X', ξ', f, ?_, hirr', hdom, hsm⟩
  rw [hseg]
  convert coordTie_comp_equiv hx' (segIxEquiv (Ψ := CMType H) (p := D.p) (q := D.q) (n := n) (J₀ := J₀)) using 1 <;> exact Subsingleton.elim _ _
end
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar GlobalTheory.CompanionTheory.Ar.TieArith ReciprocityTheory.ChartRestriction.G.AI.I4

section Comparison₂

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
  {K : Type} [Fintype K] {J : K → Type}

theorem exists_chart (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) :
    ∃ c : ∀ k, J k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  exact ⟨c, fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)⟩

theorem ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (h : CoordTie ℤ ξ (seg y)) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : ratioField y c = ⊤ := by
  have hne : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, u, hu, -, rfl⟩ := FracChart.exists_eq_div_adjoin X Ω ξ _ (seg y) c h hne a
  exact div_mem (adjoin_le_ratioField y c hg) (adjoin_le_ratioField y c hu)

theorem trdeg_eq_of_ringKrullDim [∀ k, Fintype (J k)] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hdim : ringKrullDim (MRing J ⧸ mCoordIdeal y) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    Algebra.trdeg ℤ Ω = d := by
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = Algebra.trdeg ℤ Ω := by
    rw [hb]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  have h2 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat =
      ((d + Fintype.card K : ℕ) : ℕ∞) := by
    generalize (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat = e at h1
    cases e using ENat.recTopCoe with
    | top => exact absurd h1 (by rw [top_add]; exact (ENat.natCast_ne_top _).symm)
    | coe e =>
      have h3 : e + 1 = d + 1 + Fintype.card K := by exact_mod_cast h1
      have h4 : e = d + Fintype.card K := by omega
      rw [h4]
  have h5 : Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal) = ((d + Fintype.card K : ℕ) : Cardinal) :=
    Cardinal.toENat_eq_natCast.mp h2
  rw [Nat.cast_add] at h5
  exact (Cardinal.add_nat_inj _).mp h5

end Comparison₂

theorem isArithVar_xb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d _ hT hA
  obtain ⟨c₀, hc₀⟩ := exists_chart 𝔐.ξ x₀ 𝔐.tie
  obtain ⟨cb, hcb⟩ := exists_chart 𝔐.ξ _ hT
  have hd : Algebra.trdeg ℤ Ω = d :=
    trdeg_eq_of_ringKrullDim x₀ c₀ hc₀ (ratioField_eq_top 𝔐.ξ x₀ 𝔐.tie c₀ hc₀) d hA.2.2.2
  obtain ⟨k₀⟩ := hA.1
  have hK : Nonempty (NonPluckerBlocks (blkF (CMType H) D.p D.q K₀)) := by
    refine ⟨⟨.inl k₀, fun r ↦ ?_⟩⟩
    unfold blkF
    split <;> simp
  exact isArithVar_of_ratioField_eq_top _ cb hcb (ratioField_eq_top 𝔐.ξ _ hT cb hcb) d hd

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flag_isArithVar_and_image : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ :=
  @PositivityTheory.Xgp.t_fl_arith

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix


theorem _root_.GlobalTheory.T.regularized_weight_uniform_on_compact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Xo : Set ((Σ k, ι k) → ℂ)) (B : HermLine ι) (S : LogLogRegularisationSetting M Xo B), S.IsTied → ∀ K' ⊆ S.R.Yo, IsCompact K' → TendstoUniformlyOn S.regWeight S.R.ph (𝓝[>] 0) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendstoUniformlyOn_regWeight_of_isCompact_subset_Yo <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem packing : PackingStatement := MultiProjectiveCoordinates.packing_statement

end GlobalTheory.CompanionTheory.Ar.Small
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.exists_analytic_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → SmoothGenericFibreM y → Nonempty (AnLogRes (mCoordIdeal y) ⊤ D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | exact GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre <;> assumption)
end
