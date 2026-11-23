module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
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
import Mathlib.RingTheory.TotallySplit
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

namespace GlobalTheory.HSCore.CompShare

theorem share_of_data {F : Type} [Field F] [NumberField F] (X : Data F) {D δ T d : ℕ} (hD : X.D = D) (hT : X.T = T)
    (hd : X.d = d) (hδ : (δ : ℤ) = X.del) (h : (X.R : ℤ) * X.del ≤ X.d) : (T - 1).choose D * δ ≤ d := by
  subst hD hT hd
  rw [← hδ] at h
  exact_mod_cast h

theorem choose_mul_compDeg_le : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), IsNef c.F (h.data f₁ f₂ th k).LA → IsBig c.F (h.data f₁ f₂ th k).LA → (h.data f₁ f₂ th k).Birational → (P.T - 1).choose (CompHt.dimFlag Dw) * CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0) ≤ Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hn hb hB
  have hp := GlobalTheory.CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  have e := GlobalTheory.HSCore.ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _
    (h.data f₁ f₂ th k).geom hB hp.2
  refine share_of_data (h.data f₁ f₂ th k) hD rfl (h.d_eq f₁ f₂ th k) ?_ (GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le hQ c.F _ hn hb)
  rw [← e, CompHt.compDeg, ← hD]

end GlobalTheory.HSCore.CompShare
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.FlatCM.GramExists

theorem exists_weilEq_entry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (p q : ℕ), ρ ^ 2 = -(H.d : 𝓞 K) → p + q = 1 →
    HasType H A.t.act ρ p q → ∀ (f₁ f₂ : A.t.G ⟶ B.t.G), Serre.IsLinearHom A.t.act B.t.act f₁ →
    Serre.IsLinearHom A.t.act B.t.act f₂ → ∃ g : 𝓞 E, WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ ρ σ₁ A B p q hρ hpq hA f₁ f₂ h₁ h₂
  obtain ⟨A', B', f₁', f₂', p', q', hpq', hdet, h₁', h₂', hW⟩ := GlobalTheory.T.exists_complex_fibre_linear_homs_principalCMTriple E H K ρ σ₁ A B p q hρ hA f₁ f₂ h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_weil_pairing_eq_cm_integer_of_pure_type E H A' B' p' q' (hpq'.trans hpq) hdet f₁' f₂' h₁' h₂'
  exact ⟨g, hW g hg⟩

theorem exists_isGram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  intro E _ _ _ H K _ _ ρ σ₁ p q X
  have hP : ∀ a b : Fin p, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L
      ((X.A true).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP _ _ (X.lin (Sum.inl a)) (X.lin (Sum.inl b))
  have hQ : ∀ a b : Fin q, ∃ g : 𝓞 E, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L
      ((X.A false).t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := fun a b =>
    exists_weilEq_entry E H K ρ σ₁ (X.A false) X.B 0 1 X.ρ_sq rfl X.typeM _ _ (X.lin (Sum.inr a)) (X.lin (Sum.inr b))
  choose gP hgP using hP
  choose gQ hgQ using hQ
  exact ⟨Matrix.of gP, Matrix.of gQ, fun a b => hgP a b, fun a b => hgQ a b⟩

end GlobalTheory.FlatCM.GramExists

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.det_derivatives_borelFrameChange_canonicalWeight : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  first | exact @GlobalTheory.CompHS.det_der_frBor | exact GlobalTheory.CompHS.det_der_frBor | (intros; apply GlobalTheory.CompHS.det_der_frBor <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.det_derivatives_tangentLift_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K}
    (hz : z ≫ toFlag M = X.ptY Q) {v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) Q v) {zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (i : M.K.bundle.ι) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzO : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hJ : evalPt z O hzO (M.K.jacobian i hO g) ≠ 0), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det ≠ 0 := by
  first | exact @GlobalTheory.CompHS.det_tanLift_ne_zero | exact GlobalTheory.CompHS.det_tanLift_ne_zero | (intros; apply GlobalTheory.CompHS.det_tanLift_ne_zero <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTr

theorem extEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (e : V →ₗ[ℂ] V) (h : Set.BijOn e S S) :
    ∃ T : V ≃ₗ[ℂ] V, (∀ x ∈ S, T x = e x) ∧ ∀ x, x ∈ S ↔ T x ∈ S := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  let f : V →ₗ[ℂ] V := LinearMap.ofIsCompl hQ (e ∘ₗ S.subtype) Q.subtype
  have dec : ∀ x : V, ∃ s ∈ S, ∃ q ∈ Q, x = s + q := fun x => by
    have : x ∈ S ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨s, hs, q, hq, rfl⟩
  have hf : ∀ s ∈ S, ∀ q ∈ Q, f (s + q) = e s + q := fun s hs q hq => by
    rw [map_add (f := _), LinearMap.ofIsCompl_apply_left hQ (⟨s, hs⟩ : S), LinearMap.ofIsCompl_apply_right hQ (⟨q, hq⟩ : Q)]
    rfl
  have hdisj : ∀ y ∈ S, y ∈ Q → y = 0 := fun y h1 h2 => by
    have := hQ.inf_eq_bot
    exact (Submodule.mem_bot ℂ).1 (this ▸ Submodule.mem_inf.2 ⟨h1, h2⟩)
  have hmem : ∀ x, x ∈ S ↔ f x ∈ S := by
    intro x
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    rw [hf s hs q hq]
    constructor
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx hs) hq
      subst hq0
      simpa using h.mapsTo hs
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx (h.mapsTo hs)) hq
      subst hq0
      simpa using hs
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxS : x ∈ S := (hmem x).2 (hx ▸ S.zero_mem)
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hxS hs) hq
    subst hq0
    rw [add_zero] at hx ⊢
    have h0 := hf s hs 0 Q.zero_mem
    rw [add_zero, add_zero] at h0
    rw [h0] at hx
    exact h.injOn hs S.zero_mem (by rw [hx, map_zero])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨s', hs', q, hq, rfl⟩ := dec y
    obtain ⟨s, hs, rfl⟩ := h.surjOn hs'
    exact ⟨s + q, hf s hs q hq⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x hx => ?_, hmem⟩
  show f x = e x
  have := hf x hx 0 Q.zero_mem
  rwa [add_zero, add_zero] at this

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem exists_isWeil_trans : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.model_evaluation_bijective_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.model_evaluation_preserves_admissible hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (GlobalTheory.T.model_evaluation_preserves_schwartz hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.model_evaluation_intertwines hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end GlobalTheory.ModelTr

end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

theorem _root_.GlobalTheory.T.thetaSum_invariant_rational_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaRatPair.thetaSum_om_rat | exact GlobalTheory.ThetaRatPair.thetaSum_om_rat | (intros; apply GlobalTheory.ThetaRatPair.thetaSum_om_rat <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolDense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_pol_of_isGauss (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem mem_pol_of_actsD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h


open scoped Classical in
theorem pol_stable (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (v a : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h₁ : ∀ y, f₁ y = fderiv ℝ (⇑f) y v - 2 * Real.pi * Complex.I * (GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a : ℂ) * f y) :
    f₁ ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, hD⟩ := GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq M ψ hψ (v, a)
  obtain ⟨D, hDa⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
  have e : D f = f₁ := by
    refine SchwartzMap.ext fun y => ?_
    rw [hD f (D f) (hDa f) y, h₁ y]
  exact e ▸ mem_pol_of_actsD M ψ τ hu hf (hDa f)


open scoped Classical in
theorem pol_dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨g, hg, Q, c, hc, hQ, hgQ⟩ := GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair F E σ B n d X W M χX χW om r s r' s' hP
  refine GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ _ g Q c hc hQ hgQ (mem_pol_of_isGauss M B.ψ B.emb hg) ?_ ?_
  · intro v f f₁ hf h₁
    refine pol_stable M B.ψ hψ B.emb v 0 hf fun y => ?_
    rw [h₁ y]
    simp [GlobalTheory.ArchUniq.trP]
  · intro ℓ f f₁ hf h₁
    have hnd := GlobalTheory.ArchSch.mixedTracePairing_nondegenerate F (Fin n × Fin d)
    obtain ⟨a, ha⟩ : ∃ a, ∀ y, GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a = ℓ y := by
      let e := (GlobalTheory.ArchSch.trP F (Fin n × Fin d)).flip.toDual hnd.flip
      refine ⟨e.symm ℓ.toLinearMap, fun y => ?_⟩
      calc GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y (e.symm ℓ.toLinearMap) = e (e.symm ℓ.toLinearMap) y := by
            simp only [e, LinearMap.BilinForm.toDual_def]; rfl
        _ = ℓ y := by rw [e.apply_symm_apply]; rfl
    have hmem : (-(2 * Real.pi * Complex.I)) • f₁ ∈ M.Pol B.ψ B.emb := by
      refine pol_stable M B.ψ hψ B.emb 0 a hf fun y => ?_
      simp [h₁ y, ha y]
      ring
    have hne : (-(2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (M.Pol B.ψ B.emb).smul_mem (-(2 * Real.pi * Complex.I))⁻¹ hmem
    rwa [inv_smul_smul₀ hne] at this

end GlobalTheory.PolDense
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory GlobalTheory.ChartGlue

namespace GlobalTheory.Mean4O.CoverInt

theorem volume_image_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → (∀ W : X.Opens, Nonempty W → Function.Injective (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p W)) → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (D : ℕ) (c : AlgChart p σ D), MeasureTheory.volume (c.e '' (c.e.source ∩ (ptsIn p σ U)ᶜ)) = 0 := by
  intro k _ X _ p σ hσ _ U hU D c
  have : IsDomain k := hσ.isDomain σ
  refine measure_mono_null ?_ (ae_iff.1 (SemiPosBir.ae_mem hσ c (U := U) ⟨_, hU⟩))
  rintro _ ⟨z, hz, rfl⟩ h
  have h₁ := h (c.e.map_source hz.1)
  rw [c.e.left_inv hz.1] at h₁
  exact hz.2 h₁

end GlobalTheory.Mean4O.CoverInt
end
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ g : Sec s U.1 →+* C, spMap g ≫ affPt s U = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x U.2 (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  refine ⟨(x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom, ?_⟩
  change Spec.map (x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫ U.2.fromSpec = x
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_spMap_eq {A C : Type} [CommRing A] [CommRing C] {g g' : A →+* C} (h : spMap g = spMap g') : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eq_of_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] {g g' : Sec s U.1 →+* C} (h : spMap g ≫ affPt s U = spMap g' ≫ affPt s U) : g = g' := by
  have : Mono (affPt s U) := @IsOpenImmersion.mono _ _ _ (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  exact eq_of_spMap_eq ((cancel_mono _).1 h)

theorem red_over (D : Data) : D.i ≫ D.s = D.t := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  rw [ht, hpb.w]

variable {D : Data} (Λ : Lift D)

theorem Lift.isDPMorphism (U : AffOp D.X) (T : Thick D.κ D.t) (φ : (Λ.L.obj U).B →ₐ[D.R] T.B) :
    IsDPMorphism (Λ.L.obj U).δ T.δ (φ : (Λ.L.obj U).B →+* T.B) := by
  have hI : ∀ r ∈ D.I, algebraMap D.R T.B r ∈ T.J := fun r hr ↦ T.dp.1 (Ideal.mem_map_of_mem _ hr)
  refine IsDPMorphism.on_span (S := algebraMap D.R (Λ.L.obj U).B '' D.I) _ _ (Λ.gen U) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simpa using hI r hr
  · rintro n _ ⟨r, hr, rfl⟩
    rw [(Λ.L.obj U).dp.2 r hr]
    simpa using (T.dp.2 (n := n) r hr).symm

theorem Lift.hom_iff (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B) :
    spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔
      ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a := by
  constructor
  · intro h
    let φ : (Λ.L.obj U).B →ₐ[D.R] T.B := y.comp (Λ.e U).symm.toAlgHom
    have hφ : ∀ a, φ (Λ.e U a) = y a := fun a ↦ by simp [φ]
    have hd := Λ.isDPMorphism U T φ
    let φ₀ : (Λ.L.obj U).B₀ →+* T.B₀ := RingHom.liftOfSurjective (Λ.L.obj U).π (Λ.L.obj U).surj
      ⟨T.π.comp (φ : (Λ.L.obj U).B →+* T.B), fun b hb ↦
        (T.ker _).2 (hd.1 (Ideal.mem_map_of_mem _ (((Λ.L.obj U).ker b).1 hb)))⟩
    have hc : ∀ b, φ₀ ((Λ.L.obj U).π b) = T.π (φ b) := fun b ↦
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ b
    refine ⟨⟨φ, φ₀, hc, hd, ?_⟩, hφ⟩
    have := D.mono_i
    rw [← cancel_mono D.i, Category.assoc, ← Λ.pt U, ← h, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ (hc _).trans (congrArg T.π (hφ a))
  · rintro ⟨b, hb⟩
    rw [← b.pt, Category.assoc, ← Λ.pt U, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ ((b.comm _).trans (congrArg T.π (hb a))).symm

theorem Lift.hom_spec : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  intro D Λ
  refine ⟨Λ.hom_iff, fun U T h ↦ ?_, fun U C _ g g' h ↦ eq_of_spMap_affPt _ _ h, ?_⟩
  · obtain ⟨g, hg⟩ := exists_spMap_affPt D.s U.unop _ h
    refine ⟨g, hg, fun r ↦ ?_⟩
    have : spMap (g.comp (algebraMap D.R (Sec D.s U.unop.1))) = spMap (T.π.comp (algebraMap D.R T.B)) := by
      rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, hg, Category.assoc, red_over, T.w]
    exact RingHom.congr_fun (eq_of_spMap_eq this) r
  · obtain ⟨N₀, h⟩ := (isDPNilpotent_iff_exists_isLevel D.κ).1 D.nil
    refine ⟨N₀, fun N hN U ↦ ?_⟩
    have h' : fil D.κ N = ⊥ := eq_bot_iff.2 (le_of_le_of_eq (ExpBij.dpFil_anti D.κ hN) h)
    have := fil_le_map_fil _ _ D.κ _ _ (Λ.L.obj U).δ _ (Λ.L.obj U).dp (Λ.gen U) N
    rw [h', Ideal.map_bot] at this
    exact eq_bot_iff.2 this

end GlobalTheory.PDForm
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧ Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  first | exact @GlobalTheory.PDForm.pull_isSm_bijective | exact GlobalTheory.PDForm.pull_isSm_bijective | (intros; apply GlobalTheory.PDForm.pull_isSm_bijective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ b, ctr v (algebraMap B (DR R B) b) = 0) ∧ (∀ ω, ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω)) ∧ (∀ x y, ctr v (x * y) = ctr v x * y + sgn x * ctr v y) ∧ (∀ x, ctr v (ctr v x) = 0) ∧ (∀ x, ctr v (sgn x) = -sgn (ctr v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], ctr v x ∈ ⋀[B]^j Ω[B⁄R]) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (v : Derivation R B B), (∀ x y, lie v (x * y) = lie v x * y + x * lie v y) ∧ (∀ b, lie v (algebraMap B (DR R B) b) = algebraMap B (DR R B) (v b)) ∧ (∀ b, lie v (ι1 (D R B b)) = ι1 (D R B (v b))) ∧ (∀ x, lie v (dDR R B x) = dDR R B (lie v x)) ∧ (∀ x, lie v (ctr v x) = ctr v (lie v x)) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[B]^j Ω[B⁄R], lie v x ∈ ⋀[B]^j Ω[B⁄R] := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rules | exact GlobalTheory.PDForm.ctr_lie_rules | (intros; apply GlobalTheory.PDForm.ctr_lie_rules <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.smoothLift_comparisonRelations_add_smul : ∀ (D : Data) (Λ : Lift D), (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧ (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧ (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧ ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  first | exact @GlobalTheory.PDForm.rel_add_smul | exact GlobalTheory.PDForm.rel_add_smul | (intros; apply GlobalTheory.PDForm.rel_add_smul <;> assumption)
end
