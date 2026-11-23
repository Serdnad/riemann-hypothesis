module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
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
import Mathlib.RingTheory.AdicCompletion.Topology
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isComplAt_ringEquiv_comp {A R S : Type} [CommRing A] [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (ψ : A →+* R) (σ : R ≃+* S) (h : IsComplAt ψ) : IsComplAt ((σ : R →+* S).comp ψ) := by
  obtain ⟨hN, hC, hF, hM, hR⟩ := h
  have hmap : (maximalIdeal R).map σ = maximalIdeal S := map_ringEquiv_maximalIdeal σ
  have hcomap : (maximalIdeal S).comap (σ : R →+* S) = maximalIdeal R := by
    rw [← hmap]; exact Ideal.comap_map_of_bijective _ σ.bijective
  refine ⟨isNoetherianRing_of_ringEquiv R σ, ?_, ?_, ?_, ?_⟩
  · haveI := hC
    rw [← hmap, IsAdicComplete.congr_ringEquiv]; exact hC
  · exact RingHom.Flat.comp hF (RingHom.Flat.of_bijective σ.bijective)
  · rw [← Ideal.comap_comap, hcomap, ← Ideal.map_map, hM]; exact hmap
  · intro s
    obtain ⟨a, b, hb, hab⟩ := hR (σ.symm s)
    refine ⟨a, b, ?_, ?_⟩
    · simpa using hb.map (σ : R →+* S)
    · have : (σ : R →+* S) (σ.symm s * ψ b - ψ a) ∈ maximalIdeal S := by
        rw [← Ideal.mem_comap, hcomap]; exact hab
      simpa using this

theorem exists_chartRing_factor : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W], Nonempty (ℚ →+* W) → ∀ (m N : ℕ) (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial (Fin m ⊕ Fin N) W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → (∀ i, ψV (MvPolynomial.X (.inl i)) ∈ maximalIdeal V) → ∃ (k : Type) (_ : Field k) (e : ℕ) (ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* ChartRing k m e) (θ : ChartRing k m e →+* V), GlobalTheory.TChart.IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) ∧ ∀ i, ψ (MvPolynomial.X (.inl i)) = bdParam k m e i := by
  intro W _ _ hQ m N V _ _ hV ψV hCV hXV
  obtain ⟨R, _, _, _, ψ, θ, hψ, hθ, hθψ, hψC⟩ :=
    exists_complAt_factor_of_isAdicComplete W (Fin m ⊕ Fin N) V hV ψV hCV
  obtain ⟨hreg, -⟩ := isRegularLocalRing_and_isDomain_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC
  haveI := hreg
  let t : Fin m → R := fun i => ψ (MvPolynomial.X (.inl i))
  have ht : ∀ i, t i ∈ maximalIdeal R := by
    intro i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (θ (t i)) := hu.map θ
    have h2 : θ (t i) = ψV (MvPolynomial.X (.inl i)) := by
      show (θ.comp ψ) _ = _; rw [hθψ]
    rw [h2] at h1
    exact (mem_maximalIdeal _).1 (hXV i) h1
  have hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha i
    exact cotangent_indep_of_isComplAt W (Fin m ⊕ Fin N) R ψ hψ hψC m (Function.Embedding.inl) ht a
      (Ideal.mem_sup_left ha) i
  have hQR : Nonempty (ℚ →+* R) := ⟨(ψ.comp MvPolynomial.C).comp hQ.some⟩
  obtain ⟨k, _, e, σ, hσ⟩ := GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters R hψ.2.1 hQR m t ht hind
  refine ⟨k, inferInstance, e, (σ : R →+* ChartRing k m e).comp ψ, θ.comp (σ.symm : ChartRing k m e →+* R),
    isComplAt_ringEquiv_comp ψ σ hψ, inferInstance, ?_, ?_, ?_⟩
  · rw [← hθψ]; ext x <;> simp
  · show IsLocalHom ((σ : R →+* ChartRing k m e).comp (ψ.comp MvPolynomial.C))
    infer_instance
  · intro i; exact hσ i

end GlobalTheory.TChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  first | exact @GlobalTheory.TInj.low_eq_of_match | exact GlobalTheory.TInj.low_eq_of_match | (intros; apply GlobalTheory.TInj.low_eq_of_match <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

theorem divPt_match_of_pairs : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (D₀ : DegPre R) (D₁ D₂ : DegPre V), D₀.TauBimult → D₂.TauBimult → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀ D₁) (hD₂ : IsPullDeg f₂ D₀ D₂) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.P.A ⟶ D₂.P.A) (φ' : D₁.X ≃+ D₂.X) (k : ℕ), 1 ≤ k → (∀ p₀ : QkPt D₀ F₀ k, ∃ (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (∀ y : D₀.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → ∀ (y : D₀.X) (x : TF (R := R) F₀ ⟶ D₀.P.A), x ^ k = DegPre.cF D₀ F₀ y → ∃ z : TF (R := V) F ⟶ D₁.P.A, z.left ≫ hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁) = spMap j₁ ≫ x.left ∧ z.left ≫ b.left ≫ hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂) = spMap j₂ ≫ x.left := by
  intro R V _ _ _ _ D₀ D₁ D₂ hB₀ hB₂ f₁ f₂ hD₁ hD₂ F₀ _ _ _ F _ _ j₁ j₂ b φ' k hk hpair hφ y x hx
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.T.exists_divisionPoint_pair_over_algClosed R D₀ hB₀ F₀ k hk y x hx
  obtain ⟨p₁, p₂, h₁y, hT₁, h₂y, hT₂, p', hp'y, hAct, hEq⟩ := hpair p₀
  have hy' : p'.y = p₂.y := by
    rw [hp'y, h₂y, h₁y, hp₀y]
    apply hD₂.xe.injective
    rw [hφ y, AddEquiv.apply_symm_apply]
  have hg : p'.g = p₂.g := qkPt_g_eq_of_equiv V D₂ hB₂ F k hk p' p₂ hy' hEq
  obtain ⟨g₁, ⟨hg₁b, -⟩, hP₁, -⟩ := hT₁
  obtain ⟨g₂, ⟨hg₂b, -⟩, hP₂, -⟩ := hT₂
  refine ⟨p₁.g.b, ?_, ?_⟩
  · rw [hP₁, hg₁b, hp₀b]
  · have hb : p₂.g.b = p₁.g.b ≫ b := by rw [← hg]; exact hAct.1
    rw [← Over.comp_left_assoc, ← hb, hP₂, hg₂b, hp₀b]

end GlobalTheory.TInj
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.TorusExt
attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Mum.RatChar

theorem charFixed : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hact hb χ
  let f : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing R) := σ.toAlgHom.toRingHom
  have hf : f.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := σ.toAlgHom.comp_algebraMap
  have hB := D'.tau_bimult
  obtain ⟨h, ⟨hhb, hhs⟩, ⟨z, hz, hzι⟩, hhe⟩ := GlobalTheory.T.lattice_point_nth_multiple_galois_fixed_point T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ (F.xp p₀.y)
  have hya : p.y = F.xi (F.xp p₀.y) := by rw [hy, F.xi_xp]
  have hg : n • p.g = iota hB _ p.y := by
    obtain ⟨z', hz', hz'ι⟩ := p.eq
    rw [← (isNsmul_iff_eq _ _ _).1 hz', ← (isIota_iff_eq hB _ _).1 hz'ι]
  have hh : n • h = iota hB _ p.y := by
    rw [hya, ← (isNsmul_iff_eq _ _ _).1 hz, ← (isIota_iff_eq hB _ _).1 hzι]
  set t := p.g - h with ht
  have htn : n • t = 0 := by rw [ht, nsmul_sub, hg, hh, sub_self]
  have hte : GtPtAct F.o F.e t t :=
    GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent F.o F.e F.idem p₀.g p.g h t hact hhe ((isAdd_iff_eq _ _ _).2 (sub_add_cancel p.g h).symm)
  have hfixh : gtExt D'.toPre f hf h = h := ((eq_gtExt_iff f hf h h).2 ⟨hhb.symm, hhs⟩).symm
  have hgb : extMap f hf ≫ p.g.b = p.g.b := by
    obtain ⟨b, hb⟩ := hb
    apply Over.OverMorphism.ext
    rw [Over.comp_left, extMap_left, hb, ← Category.assoc]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]
  have htb : extMap f hf ≫ t.b = t.b := by
    have e1 : gtExt D'.toPre f hf t = gtExt D'.toPre f hf p.g - h := by rw [ht, map_sub, hfixh]
    have e2 := congrArg GtPtF.b e1
    rw [gtExt_b, sub_eq_add_neg, add_b, neg_b, gtExt_b, hgb] at e2
    rw [e2, ht, sub_eq_add_neg, add_b, neg_b]
  have htb' : spMap f ≫ t.b.left = t.b.left := by
    have := congrArg (fun q => q.left) htb
    simpa [Over.comp_left, extMap_left] using this
  have hts := GlobalTheory.T.characterValues_galoisFixed_of_idempotent_torsion T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ t hte ⟨0, (isNsmul_iff_eq _ _ _).2 htn.symm, (isZero_iff_eq _).2 rfl⟩ htb'
  have hfixt : gtExt D'.toPre f hf t = t := ((eq_gtExt_iff f hf t t).2 ⟨htb'.symm, hts⟩).symm
  have hfixg : gtExt D'.toPre f hf p.g = p.g := by
    have : p.g = t + h := (sub_add_cancel p.g h).symm
    rw [this, map_add (f := _), hfixt, hfixh]
  exact ((eq_gtExt_iff f hf p.g p.g).1 hfixg.symm).2 χ

end GlobalTheory.Mum.RatChar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LevLift

theorem tauBimult_of_rescale_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ), (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)) → (GlobalTheory.PolDeg.rescale D g).TauBimult → D.TauBimult := by
  intro R _ _ D g hg h
  refine (GlobalTheory.PolDeg.QuadIff.bimult_iff D).2 fun a a' b z J hJ => ?_

  have H := (GlobalTheory.PolDeg.QuadIff.bimult_iff (GlobalTheory.PolDeg.rescale D g)).1 h a a' b z J hJ
  have e1 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ (a + a') b
  have e2 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ a b
  have e3 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ a' b
  erw [e1, e2, e3] at H
  have hc := congrArg (GlobalTheory.PolDeg.QuadIff.germU z) (hg a a' b)
  simp only [map_mul] at hc
  open GlobalTheory.PolDeg.QuadIff in
  replace H : germU z (g (a + a' + b)) * (germU z (g (a + a')))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau (a + a') b) (𝟙 _) z J *
      Geo.Tor.val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau a b) (𝟙 _) z J *
      (germU z (g (a' + b)) * (germU z (g a'))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau a' b) (𝟙 _) z J) := H
  have a1 := congrArg Additive.ofMul H
  have a2 := congrArg Additive.ofMul hc
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a1 a2 ⊢
  linear_combination (norm := abel) a1 - a2

theorem degPre_cocharPoint_nsmul_eq_pow_levelLift {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (x : D.X) (n : ℕ) : D.c (n • x) = D.c x ^ n := by
  have hmul : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => (D.c_add a b).trans (Hom.mul_def _ _).symm
  have h0 : D.c 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := D.c 0) (by rw [_root_.mul_one]; exact h.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hmul, ih, pow_succ]

theorem roots_of_pull {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D₀ : DegPre W)
    (Q : DegPre V) (hD : IsPullDeg θ D₀ Q) (y₀ : D₀.X → (𝟙_ (Over (Sp W)) ⟶ D₀.P.A)) (n : ℕ)
    (hy : ∀ x, D₀.c x = y₀ x ^ n) : ∃ c' : Q.X → (𝟙_ (Over (Sp V)) ⟶ Q.P.A), ∀ χ, c' χ ^ n = Q.c χ := by
  letI : IsIso hD.e.hom := hD.e.isIso_hom
  letI : Mono hD.e.hom := IsIso.mono_of_iso hD.e.hom
  have he := hD.e_hom
  let c'' : Q.X → (𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf θ)).obj D₀.P.A) := fun χ =>
    Over.homMk (pullback.lift (specOf θ ≫ (y₀ (hD.xe χ)).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (y₀ (hD.xe χ))]; simp)) (pullback.lift_snd _ _ _)
  refine ⟨fun χ => c'' χ ≫ hD.e.inv, fun χ => ?_⟩
  dsimp only
  rw [← cancel_mono hD.e.hom, pow_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h1 := GlobalTheory.ZH.MultInt.pow_left_pullback (specOf θ) D₀.P.A (T := 𝟙_ (Over (Sp V))) (T₀ := 𝟙_ (Over (Sp W)))
      (specOf θ) (by simp) (c'' χ) (y₀ (hD.xe χ)) (pullback.lift_fst _ _ _).symm n
    have h2 := hD.c_pr χ
    rw [← hy] at h1
    rw [← h1, Over.comp_left, Category.assoc, h2]
  · exact (Over.w (c'' χ ^ n)).trans (Over.w (Q.c χ ≫ hD.e.hom)).symm

theorem exists_roots_of_pull_mulDeg : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D : DegPre W) (n : ℕ) (Q : DegPre V), IsPullDeg θ (mulDeg D n) Q → ∃ c' : Q.X → (𝟙_ (Over (Sp V)) ⟶ Q.P.A), ∀ χ, c' χ ^ n = Q.c χ := by
  intro W V _ _ _ _ θ D n Q hD
  exact roots_of_pull θ (mulDeg D n) Q hD (fun x : D.X => D.c x) n (fun x : D.X => degPre_cocharPoint_nsmul_eq_pow_levelLift D x n)

theorem exists_lift_torsion_of_pull : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D : DegPre W) (Q : DegPre V) (hD : IsPullDeg θ D Q) (G : Over (Sp W)) [GrpObj G] (φ : G.left ⟶ D.P.A.left), IsGrpPullback G D.P.A (𝟙 _) φ → ∀ (x : 𝟙_ (Over (Sp W)) ⟶ G) (n : ℕ), x ^ n = 1 → ∃ b : TF (R := V) (FractionRing V) ⟶ Q.P.A, b ^ n = 1 ∧ b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf θ) = jK V ≫ spMap θ ≫ x.left ≫ φ := by
  intro W V _ _ _ _ θ D Q hD G _ φ hp x n hx
  letI : IsIso hD.e.hom := hD.e.isIso_hom
  letI : Mono hD.e.hom := IsIso.mono_of_iso hD.e.hom
  have he := hD.e_hom
  have hφ : φ ≫ D.P.A.hom = G.hom := by simpa using hp.1.w
  have hxφ : (x.left ≫ φ) ≫ D.P.A.hom = 𝟙 (Sp W) ≫ 𝟙 (Sp W) := by
    rw [Category.assoc, hφ, Over.w x]; simp
  let x₁ : Over.mk (𝟙 (Sp W) ≫ 𝟙 (Sp W)) ⟶ D.P.A := Over.homMk (x.left ≫ φ) hxφ
  have hx₁ : x₁ ^ n = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (t' := 𝟙 (Sp W)) rfl hp (x' := x) (x := x₁) rfl).1 hx
  have hj : jFK (R := V) (FractionRing V) = 𝟙 _ := by
    simp [jFK]
  have hc : (jK V ≫ spMap θ ≫ x.left ≫ φ) ≫ D.P.A.hom = (TF (R := V) (FractionRing V)).hom ≫ specOf θ := by
    rw [Category.assoc, Category.assoc, Category.assoc, hφ, Over.w x]
    simp [TF, hj]
  let b'' : TF (R := V) (FractionRing V) ⟶ (Over.pullback (specOf θ)).obj D.P.A :=
    Over.homMk (pullback.lift (jK V ≫ spMap θ ≫ x.left ≫ φ) (TF (R := V) (FractionRing V)).hom hc)
      (pullback.lift_snd _ _ _)
  have hb'' : b'' ^ n = 1 := by
    refine GlobalTheory.UU.ImagePairing.pow_eq_one_of_pullback (specOf θ) (T := Over.mk (𝟙 (Sp W) ≫ 𝟙 (Sp W)))
      (jK V ≫ spMap θ) ?_ (x := x₁) ?_ hx₁
    · simp [TF, hj]
    · simp only [b'', x₁, Over.homMk_left]
      exact pullback.lift_fst _ _ _
  refine ⟨b'' ≫ hD.e.inv, ?_, ?_⟩
  · rw [← cancel_mono hD.e.hom, pow_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, hb'']
    exact (one_comp _).symm
  · rw [← Over.comp_left_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [b'', Over.homMk_left]
    exact pullback.lift_fst _ _ _

end GlobalTheory.UCanon.LevLift

namespace GlobalTheory.UCanon


open GlobalTheory.UCanon.LevLift in
theorem exists_levPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivBy L Q oQ iw s ε e g hD → ∀ a : D'.La, ∃ p : QkPt Q (FractionRing V) l.M', IsLevPt L iw hD a p := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e g hD _ hs hdiv a
  have hM : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  letI := H.starRing
  have hB0 : (mulDeg L.D l.M').TauBimult :=
    (GlobalTheory.UCanon.MulDeg.mulDeg_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen).2.1
  have hB1 : (GlobalTheory.PolDeg.rescale Q g).TauBimult := GlobalTheory.TauPull.tauBimult_pull hG hD hB0
  have ht : ∀ k, algebraMap V (FractionRing V) (s k) ≠ 0 := fun k h =>
    hs k (IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero]))
  have hq : ∀ k (a a' b : Q.X), ε k (e (a + a' + b)) (H.w0 • e (a + a' + b)) + ε k (e a) (H.w0 • e a) +
      ε k (e a') (H.w0 • e a') + ε k (e b) (H.w0 • e b) = ε k (e (a + a')) (H.w0 • e (a + a')) +
      ε k (e (a + b)) (H.w0 • e (a + b)) + ε k (e (a' + b)) (H.w0 • e (a' + b)) := by
    intro k a a' b
    simp only [map_add (f := _), smul_add, LinearMap.add_apply]
    ring
  have hP : ∀ y, ((g y : (FractionRing V)ˣ) : FractionRing V) =
      (∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hdiv.1 y, Units.val_inv_eq_inv_val, inv_inv]
  have hcube : ∀ a a' b : Q.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b) := by
    intro a a' b
    apply Units.ext
    simp only [Units.val_mul, hP, ← mul_inv, ← Finset.prod_mul_distrib, ← zpow_add₀ (ht _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    linear_combination (l.M' : ℤ) * hq k a a' b
  have hB : Q.TauBimult := tauBimult_of_rescale_cube Q g hcube hB1
  obtain ⟨c', hc'⟩ := exists_roots_of_pull_mulDeg iw L.D l.M' _ hD
  have h0 : L.o.etaA 0 = 1 := by
    have h := L.o.etaA_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := L.o.etaA 0) (by rw [_root_.mul_one]; exact h.symm)
  have hn : ∀ n : ℕ, L.o.etaA (n • a) = L.o.etaA a ^ n := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, L.o.etaA_add, ih, pow_succ]
  have hη : L.o.etaA a ^ l.M' = 1 := by
    rw [← hn]
    exact L.o.etaA_ker a
  obtain ⟨b, hb, hbl⟩ := exists_lift_torsion_of_pull iw (mulDeg L.D l.M') _ hD L.o.t.G L.φB L.ab.1 (L.o.etaA a) l.M' hη
  obtain ⟨p, hp0, hpb⟩ := GlobalTheory.T.exists_torusExtension_torsion_lift_zero Q hB l.M' hM c' hc' (FractionRing V) b hb
  exact ⟨p, hp0, by rw [hpb]; exact hbl⟩

end GlobalTheory.UCanon
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem norm_natCast_padicInt (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : n ≠ 0) :
    ‖((n : ℕ) : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n : ℤ)) := by
  rw [PadicInt.norm_def]
  push_cast
  have h := Padic.eq_padicNorm (p := l) (n : ℚ)
  push_cast at h
  rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn)]
  push_cast
  rw [Nat.padicValNat_def, padicValRat_of_nat]

theorem norm_deg_eq_norm_det : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
    ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f.asHom hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, norm_natCast_padicInt l hpos.ne']
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.padicNorm_degree_eq_padicNorm_det_tateModule : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), ‖((deg (A := A) (B := A) f.asHom : ℕ) : ℤ_[l])‖ = ‖LinearMap.det (tend l A f)‖ := by
  intro K _ l _ hl A f
  obtain ⟨hfree, hfin, -, hVfin, -⟩ := tl_free_finrank K l hl A
  by_cases hf : IsIsogeny (A := A) (B := A) f.asHom
  · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A f.asHom hf
    obtain ⟨-, hcard⟩ :=
      GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A f.asHom hf
    have hdet := GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A)
      (tmap l A A f.asHom) (padicValNat l (deg f.asHom)) hcard
    have hnorm : ‖((deg f.asHom : ℕ) : ℤ_[l])‖ =
        (l : ℝ) ^ (-(padicValNat l (deg f.asHom) : ℤ)) := by
      rw [PadicInt.norm_def]
      push_cast
      have h := Padic.eq_padicNorm (p := l) (deg f.asHom : ℚ)
      push_cast at h
      rw [h, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hpos.ne'), padicValRat.of_nat,
        Rat.cast_zpow, Rat.cast_natCast, Nat.padicValNat_def]
    change _ = ‖LinearMap.det (tmap l A A f.asHom)‖
    rw [hdet, hnorm]
  · have hdeg : deg (A := A) (B := A) f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
    by_contra hne
    apply hf
    rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A f.asHom).2]
    have hu : IsUnit (LinearMap.det (vmap l f.asHom)) := by
      rw [vmap, LinearMap.det_baseChange]
      exact (isUnit_iff_ne_zero).2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
    rw [← LinearMap.isUnit_iff_isUnit_det] at hu
    exact (Module.End.isUnit_iff _).1 hu
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


theorem _root_.GlobalTheory.T.exists_finite_regular_thetaSetup_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  first | exact @GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | exact GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | (intros; apply GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.refine_polarised_monomial_periods_monomial_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  first | exact @GlobalTheory.PolDeg.refine_monomial_of_polarised | exact GlobalTheory.PolDeg.refine_monomial_of_polarised | (intros; apply GlobalTheory.PolDeg.refine_monomial_of_polarised <;> assumption)
end
