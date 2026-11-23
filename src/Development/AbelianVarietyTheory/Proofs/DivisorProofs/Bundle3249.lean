module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3212
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Noetherian.Nilpotent
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle005

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem canon_residue_dim : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), Canon C → ((residue (ChartRing k m e)).comp C.b).EssFiniteType ∧ (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra; ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim) := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hC
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ringKrullDim_add_trdeg_completion_polynomial c.F hC.L.W (ChartRing k m e) hC.L.b hC.L.ft (Fin C.m ⊕ Fin hC.N) hC.ψ hC.compl hC.ψ_loc
    C.b hC.base
  refine ⟨h1, ?_⟩
  obtain ⟨a, t, ha, ht, hat⟩ := hC.L.dim
  obtain ⟨a', t', ha', ht', hat'⟩ := h2 a t ha ht
  have hdimR : ringKrullDim (ChartRing k m e) = ((m + e : ℕ) : WithBot ℕ∞) := by
    rw [GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries k (Fin m ⊕ Fin e), ringKrullDim_eq_zero_of_field]
    simp [Nat.card_sum]
  have hma : a' = m + e := by
    rw [hdimR] at ha'
    exact_mod_cast ha'.symm
  have hcard : Fintype.card (Fin C.m ⊕ Fin hC.N) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) hC.L.D.X *
      Module.finrank (𝓞 E) hC.L.D.X := by
    rw [← GlobalTheory.T.finrank_balancedSymmIntBilinForms_eq H hC.L.D.X, Module.finrank_eq_card_basis hC.ε]
  have hr : Module.finrank (𝓞 E) C.P.D.toPre.X = Module.finrank (𝓞 E) hC.L.D.X := hC.e.finrank_eq
  have hp := hC.hp
  have hq := hC.hq
  rw [hr] at hp hq
  have key : a' + t' = Dw.dim := by
    rw [hat', hat, hcard, Datum.dim, Datum.dim, ← hp, ← hq]
    ring
  rw [ht', ← hma]
  exact_mod_cast key

end GlobalTheory.UCanon
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UnitOpen

theorem zpow_mul_toNat {F : Type} [Field F] {x : F} (hx : x ≠ 0) (m : ℤ) :
    x ^ m * x ^ (-m).toNat = x ^ m.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have := Int.toNat_sub_toNat_neg m
  omega

theorem psiUnitOn_basicOpen_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X), DivFrom L Q oQ iw s ε e → ∀ f : V, (∀ k, ∃ n : ℕ, s k ∣ f ^ n) → ∀ y, PsiUnitOn Q y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e hdiv f hf y
  obtain ⟨g, hD, hg, -, -⟩ := hdiv
  have h1 : ∀ χ, PsiUnitOn (mulDeg L.D l.M') χ Set.univ := fun χ => L.gen (l.M' • χ)
  have h2 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y Set.univ := GlobalTheory.T.psiUnitOn_univ_of_pullback_generating _ _ _ _ _ hD h1 y
  have h3 : PsiUnitOn (GlobalTheory.PolDeg.rescale Q g) y (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) :=
    fun j W hW _ => h2 j W hW (Set.subset_univ _)
  by_cases hf0 : f = 0
  · subst hf0
    refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ 0 0 (by simp) (fun p hp => ?_) h3
    exact ((hp : (0 : V) ∉ (p : PrimeSpectrum V).asIdeal) (Ideal.zero_mem _)).elim
  set m : I → ℤ := fun k => (l.M' : ℤ) * ε k (e y) (H.w0 • e y) with hm
  have hs : ∀ k, s k ≠ 0 := fun k hk => by
    obtain ⟨n, hn⟩ := hf k
    rw [hk, zero_dvd_iff] at hn
    exact hf0 (pow_eq_zero_iff'.1 hn).1
  refine GlobalTheory.T.psiUnitOn_of_rescaled_psiUnitOn V Q g y _ (∏ k, s k ^ (m k).toNat) (∏ k, s k ^ (-m k).toNat) ?_ (fun p hp => ?_) h3
  · have hy := hg y
    have hgy : ((g y : (FractionRing V)ˣ) : FractionRing V) = (∏ k, algebraMap V (FractionRing V) (s k) ^ m k)⁻¹ := by
      rw [← hy, Units.val_inv_eq_inv_val, inv_inv]
    have hne : ∀ k, algebraMap V (FractionRing V) (s k) ≠ 0 := fun k =>
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (hs k)
    rw [hgy, map_prod, map_prod, inv_mul_eq_iff_eq_mul₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, zpow_mul_toNat (hne k)]
  · have hp' : f ∉ (p : PrimeSpectrum V).asIdeal := hp
    have hk : ∀ k, s k ∉ (p : PrimeSpectrum V).asIdeal := fun k hk => by
      obtain ⟨n, hn⟩ := hf k
      exact hp' ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem n (Ideal.mem_of_dvd _ hn hk))
    constructor <;>
    · intro hmem
      obtain ⟨k, -, hk'⟩ := ((p : PrimeSpectrum V).isPrime.prod_mem_iff).1 hmem
      exact hk k ((p : PrimeSpectrum V).isPrime.mem_of_pow_mem _ hk')

end GlobalTheory.UnitOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.PerCoord

theorem comp_C_injective {W R σ : Type} [CommRing W] [IsLocalRing W] [CommRing R] [IsLocalRing R]
    (ψ : MvPolynomial σ W →+* R) (hf : ψ.Flat) (hl : IsLocalHom (ψ.comp MvPolynomial.C)) :
    Function.Injective (ψ.comp MvPolynomial.C) := by
  have hC : (MvPolynomial.C : W →+* MvPolynomial σ W).Flat := by
    show (algebraMap W (MvPolynomial σ W)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h := RingHom.Flat.comp hC hf
  letI := (ψ.comp MvPolynomial.C).toAlgebra
  haveI : Module.Flat W R := h
  haveI : IsLocalHom (algebraMap W R) := hl
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := R)
  exact FaithfulSMul.algebraMap_injective W R

theorem prod_zpow_add {K Ix : Type} [Field K] [Fintype Ix] (c : Ix → K) (hc : ∀ k, c k ≠ 0) (A B C D : Ix → ℤ)
    (h : ∀ k, A k = D k + B k + C k) :
    ∏ k, c k ^ A k = (∏ k, c k ^ D k) * (∏ k, c k ^ B k) * ∏ k, c k ^ C k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h k, zpow_add₀ (hc k), zpow_add₀ (hc k)]

end GlobalTheory.UCanon.PerCoord

namespace GlobalTheory.UCanon.PerCoord

theorem second_diff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (e : X ≃ₗ[𝓞 E] Y) {β : LinearMap.BilinForm ℤ Y}
    (hβ : β ∈ balForms H.bar Y) (a b : X) :
    β (e (a + b)) (H.w0 • e (a + b)) = β (e a) (e b) + β (e a) (H.w0 • e a) + β (e b) (H.w0 • e b) := by
  have h1 : β (e b) (H.w0 • e a) = β (e a) (H.bar H.w0 • e b) := (hβ.1 _ _).trans (hβ.2 _ _ _)
  have h2 : β (e a) (H.w0 • e b) + β (e a) (H.bar H.w0 • e b) = β (e a) (e b) := by
    rw [← map_add (f := _), ← add_smul, ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply]
  rw [h1]
  linarith

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn
  classical
  obtain ⟨g, hD, hg, -, -⟩ := Cn.data
  have hinj := comp_C_injective Cn.ψ Cn.compl.2.2.1 Cn.ψ_loc
  obtain ⟨-, hb, hU, -⟩ := letI := H.starRing
    GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨τ₁, hτ, hF⟩ := GlobalTheory.UTautData.gens_fromBase _ hinj _ _ hD hb hU
  refine ⟨Cn.ε.map (pullBalEquiv H.bar Cn.e), τ₁, fun k => rfl, hF, fun a b => ?_⟩
  have hs : ∀ k, algebraMap R (FractionRing R) (Cn.ψ (MvPolynomial.X k)) ≠ 0 := by
    intro k
    refine (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ?_
    rcases k with i | k
    · rw [Cn.bd i]; exact C.s_ne_zero i
    · exact (Cn.tor k).ne_zero
  refine ⟨(hτ a b).1, g a * g b * (g (a + b))⁻¹, ?_, fun z J hJ => ?_⟩
  · have hsplit := prod_zpow_add _ hs
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e (a + b)) (H.w0 • Cn.e (a + b)))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (H.w0 • Cn.e a))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e b) (H.w0 • Cn.e b))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (Cn.e b))
      (fun k => by simp only [second_diff H Cn.e (Cn.ε k).2 a b]; ring)
    have hne : ∀ y, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := fun y => Units.ne_zero _
    have e1 : (((g a * g b * (g (a + b))⁻¹ : (FractionRing R)ˣ)) : FractionRing R) =
        (((g (a + b))⁻¹ : (FractionRing R)ˣ) : FractionRing R) * ((((g a)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ *
          ((((g b)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]; ring
    have hA := hne a
    have hB := hne b
    rw [hg a] at hA
    rw [hg b] at hB
    rw [e1, hg (a + b), hsplit, hg a, hg b]
    beta_reduce at hA hB ⊢
    have canc : ∀ T x y : FractionRing R, x ≠ 0 → y ≠ 0 → T * x * y * x⁻¹ * y⁻¹ = T := fun T x y hx hy => by
      field_simp
    rw [canc _ _ _ hA hB]
    refine Eq.trans ?_ (Equiv.prod_comp finSumFinEquiv.symm (fun k => algebraMap R (FractionRing R)
      (Cn.ψ (MvPolynomial.X k)) ^ (((l.M' : ℤ) • ((Cn.ε.map (pullBalEquiv H.bar Cn.e)) k :
        LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b))).symm
    exact Finset.prod_congr rfl fun k _ => rfl
  · have h1 := GlobalTheory.TauTwist.val_tau_rescale (D := C.P.D.toPre) g (a := a) (b := b)
      (x := (g a * g b)⁻¹ * g (a + b)) (by group) (𝟙 _) hJ
    have h2 := (hτ a b).2 z J hJ
    have hx : g a * g b * (g (a + b))⁻¹ = ((g a * g b)⁻¹ * g (a + b))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hx]
    show _ = GlobalTheory.TauTwist.unitAt (𝟙 _) z _ * _
    rw [map_inv]
    exact eq_inv_mul_of_mul_eq (h1.symm.trans h2)

end GlobalTheory.UCanon.PerCoord
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generating_degenerationData_principalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  first | exact @GlobalTheory.UBaseData.main | exact GlobalTheory.UBaseData.main | (intros; apply GlobalTheory.UBaseData.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanonHom

theorem pullSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G)),
    (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r) →
    ∃ x : X → (T ⟶ G'), (∀ y, (x y).left ≫ φ = (x₀ y).left) ∧ (∀ y z, x (y + z) = x y * x z) ∧
      ∀ (r : O) y, x (r • y) = x y ≫ a'.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x₀ hadd hlin
  have hw : ∀ y, (x₀ y).left ≫ G.hom = T.hom ≫ f := fun y => Over.w (x₀ y)
  let x : X → (T ⟶ G') := fun y => Over.homMk (hφ.1.lift (x₀ y).left T.hom (hw y)) (hφ.1.lift_snd _ _ _)
  have hx : ∀ y, (x y).left ≫ φ = (x₀ y).left := fun y => hφ.1.lift_fst _ _ _
  have uniq : ∀ (p q : T ⟶ G'), p.left ≫ φ = q.left ≫ φ → p = q := fun p q h => by
    ext; apply hφ.1.hom_ext h; rw [Over.w p, Over.w q]
  refine ⟨x, hx, fun y z => uniq _ _ ?_, fun r y => uniq _ _ ?_⟩
  · rw [hx, hadd, hφ.2 T (x y) (x z) (x₀ y) (x₀ z) (hx y).symm (hx z).symm]
  · rw [hx, hlin, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hx]

theorem pushSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x : X → (T ⟶ G')),
    (∀ y z, x (y + z) = x y * x z) → (∀ (r : O) y, x (r • y) = x y ≫ a'.act r) →
    ∃ x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G), (∀ y, (x₀ y).left = (x y).left ≫ φ) ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧
      ∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x hadd hlin
  have hw : ∀ y, ((x y).left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := fun y => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (x y)]; rfl
  refine ⟨fun y => Over.homMk ((x y).left ≫ φ) (hw y), fun y => rfl, fun y z => ?_, fun r y => ?_⟩
  · ext
    change (x (y + z)).left ≫ φ = _
    rw [hadd]
    exact (hφ.2 T (x y) (x z) (Over.homMk _ (hw y)) (Over.homMk _ (hw z)) rfl rfl).symm
  · ext
    simp only [Over.homMk_left, Over.comp_left, hlin, Category.assoc, ha]

theorem objMap_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} {o' : Obj D l b' s'} {o : Obj D l b s} {f f' : S' ⟶ S}
    (h : f = f') (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h; exact ⟨m, rfl⟩

theorem obj_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp B}
    (h : s₁ = s₂) (o : Obj D l b s₁) : ∃ o₂ : Obj D l b s₂, ∀ {S₀ : Scheme.{0}} {B₀ : Type} [CommRing B₀] {b₀ : Base l B₀}
      {s₀ : S₀ ⟶ Sp B₀} (o₀ : Obj D l b₀ s₀) (f : S ⟶ S₀), Nonempty (ObjMap o o₀ f) → Nonempty (ObjMap o₂ o₀ f) := by
  subst h; exact ⟨o, fun _ _ h => h⟩

theorem homScheme_low : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v) := by
  intro E _ _ _ H D' l c X _ _ _ _
  have hXo : Nonempty (Moduli D' (LowDat.lowLevel l)) := by
    by_cases hpq : 1 ≤ D'.p + D'.q
    · exact GlobalTheory.Moduli.moduli_scheme_exists E H D' _ hpq
    · exact GlobalTheory.T.nonempty_moduli_of_rank_zero H D' _ (by omega)
  obtain ⟨Xo⟩ := hXo
  set sF : Sp c.F ⟶ Sp (KA (LowDat.lowLevel l)) := lowMap c (RingHom.id c.F) with hsF
  have P := GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := LowDat.lowLevel l)
  obtain ⟨oY, ⟨mY⟩⟩ := P.1 Xo.s Xo.univ (pullback.fst Xo.s sF) (pullback.snd Xo.s sF ≫ sF) pullback.condition.symm
  have hB : IsAbelianScheme oY.t.G := ⟨inferInstance, oY.t.semi.smooth, oY.proper, oY.t.semi.geomConnected⟩
  have hg := GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme D' (LowDat.lowLevel l) (pullback.snd Xo.s sF ≫ sF) oY
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int _ _
  obtain ⟨C, _, u, -, hCsm, -, hadd, hlin, huniv⟩ :=
    GlobalTheory.HomScheme.exists_homObj_relDim _ oY.t.G hB _ hg oY.t.act X
  obtain ⟨oC, ⟨mC⟩⟩ := P.1 (pullback.snd Xo.s sF ≫ sF) oY C.hom ((C.hom ≫ pullback.snd Xo.s sF) ≫ sF)
    (Category.assoc _ _ _)
  obtain ⟨u', hu'φ, hu'add, hu'lin⟩ := pullSec oC.t.G oY.t.G C.hom mC.toSABMap.φ mC.cart (𝓞 E) oC.t.act oY.t.act mC.act X
    (𝟙_ (Over C.left)) (fun y => Over.homMk (𝟙 C.left) (by simp) ≫ u y) (fun y z => by rw [hadd, comp_mul])
    (fun r y => by rw [hlin, Category.assoc])
  have key : ∀ {T : Scheme.{0}} (v₁ v₂ : T ⟶ C.left), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, v₁ ≫ (u y).left = v₂ ≫ (u y).left) → v₁ = v₂ := by
    intro T v₁ v₂ hw hu
    obtain ⟨c0, -, huq⟩ := huniv (Over.mk (v₁ ≫ C.hom)) (fun y => Over.homMk v₁ rfl ≫ u y)
      (fun y z => by rw [hadd, comp_mul]) (fun r y => by rw [hlin, Category.assoc])
    have e1 := huq (Over.homMk v₁ rfl) (fun y => rfl)
    have e2 := huq (Over.homMk v₂ hw.symm) (fun y => by ext; simpa using (hu y).symm)
    simpa using congrArg CommaMorphism.left (e1.trans e2.symm)
  have hu'l : ∀ y, (u' y).left ≫ mC.toSABMap.φ = (u y).left := fun y => by rw [hu'φ]; simp
  have key2 : ∀ (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ (v₁ v₂ : Sp A ⟶ C.left)
      (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
      (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u' y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u' y).left) → v₁ = v₂ := by
    intro A _ hA v₁ v₂ s' o'' m₁ m₂ z hw hz₁ hz₂
    obtain ⟨k₁, hk₁⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨k₂, hk₂⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hw.symm k₂
    have hφ := GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' A hA s' _ o'' oY (v₁ ≫ C.hom) k₁ k₂'
    refine key v₁ v₂ hw fun y => ?_
    calc v₁ ≫ (u y).left = z y ≫ k₁.toSABMap.φ := by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hu'l]
      _ = z y ≫ k₂'.toSABMap.φ := by rw [hφ]
      _ = v₂ ≫ (u y).left := by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hu'l]
  refine ⟨C.left, C.hom ≫ pullback.snd Xo.s sF, oC, u', ?_, hu'add, hu'lin, ?_, ?_, ?_⟩
  · haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D'.dim)
    haveI h1 : SmoothOfRelativeDimension D'.dim (pullback.snd Xo.s sF) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension D'.dim)
        (IsPullback.of_hasPullback Xo.s sF) Xo.smooth
    haveI := hCsm
    rw [add_comm]
    infer_instance
  · intro V _ _ bV o' x hxadd hxlin
    obtain ⟨f, ⟨hf, ⟨k⟩⟩, -⟩ := Xo.rep (Sp V) (lowMap c bV) inferInstance o'
    have hlow : lowMap c bV = spMap bV ≫ sF := by simp only [hsF, lowMap, spMap, ← Spec.map_comp]; rfl
    let fY : Sp V ⟶ pullback Xo.s sF := pullback.lift f (spMap bV) (hf.trans hlow)
    obtain ⟨k', -⟩ := objMap_congr (pullback.lift_fst f (spMap bV) (hf.trans hlow)).symm k
    obtain ⟨n, -⟩ := (P.2 Xo.s (pullback.snd Xo.s sF ≫ sF) (lowMap c bV) Xo.univ oY o' (pullback.fst _ _) fY mY).2 k'
    obtain ⟨x₀, hx₀, hx₀add, hx₀lin⟩ := pushSec o'.t.G oY.t.G fY n.toSABMap.φ n.cart (𝓞 E) o'.t.act oY.t.act n.act X
      (𝟙_ (Over (Sp V))) x hxadd hxlin
    obtain ⟨cc, hcc, -⟩ := huniv (Over.mk ((𝟙_ (Over (Sp V))).hom ≫ fY)) x₀ hx₀add hx₀lin
    have hccw : cc.left ≫ C.hom = fY := by simpa using Over.w cc
    obtain ⟨n', hn'⟩ := objMap_congr hccw.symm n
    obtain ⟨m, hm⟩ := (P.2 _ _ (lowMap c bV) oY oC o' C.hom cc.left mC).2 n'
    refine ⟨cc.left, m, ?_, fun y => ?_⟩
    · rw [← Category.assoc, hccw, pullback.lift_snd]
    · apply mC.cart.1.hom_ext
      · rw [Category.assoc, ← hm, hn', Category.assoc, hu'l, ← hx₀, ← hcc y]
        rfl
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (x y), Category.assoc, Over.w (u' y)]
        simp
  · intro A _ _ v₁ v₂ hv s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 A (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) v₁ v₂ s' o'' m₁ m₂ z ?_ hz₁ hz₂
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₁ ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₂ ≫ C.hom) mY).1 k₂
    have hv' := hv =≫ sF
    simp only [Category.assoc] at hv'
    have hs₁ : ((v₁ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    have hs₂ : ((v₂ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]; exact hv'.symm
    have hfst := (Xo.rep (Sp A) s' inferInstance o'').unique ⟨hs₁, ⟨K₁⟩⟩ ⟨hs₂, ⟨K₂⟩⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hv
  · intro k _ v s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 (DualNumber k) (IsNoetherianRing.isNilpotent_nilradical _) v (constPt v) s' o'' m₁ m₂ z ?_ hz₁ hz₂
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsAlgebraic ℚ c.F := Algebra.IsAlgebraic.of_finite ℚ c.F
    have hcp : ∀ {W : Scheme.{0}} (w : C.left ⟶ W), constPt v ≫ w = constPt (v ≫ w) := fun w => by simp [constPt]
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom (constPt v) mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (constPt v ≫ C.hom) mY).1 k₂
    obtain ⟨K₁', -⟩ := objMap_congr (Category.assoc v C.hom (pullback.fst Xo.s sF)) K₁
    obtain ⟨K₂', -⟩ := objMap_congr (show (constPt v ≫ C.hom) ≫ pullback.fst Xo.s sF =
      constPt (v ≫ C.hom ≫ pullback.fst Xo.s sF) by simp [constPt]) K₂
    have hs₁ : s' = (v ≫ C.hom ≫ pullback.fst Xo.s sF) ≫ Xo.s := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    obtain ⟨o₂, ho₂⟩ := obj_congr hs₁ o''
    have hfst := Xo.unram k _ o₂ (ho₂ Xo.univ _ ⟨K₁'⟩) (ho₂ Xo.univ _ ⟨K₂'⟩)
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hcp]; exact hfst
    · simp only [Category.assoc]; rw [hcp]; exact GlobalTheory.Models.RankZero.eq_constPt_field _

end GlobalTheory.UCanonHom
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


theorem _root_.GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  first | exact @GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | exact GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | (intros; apply GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_unitaryTrait_ramifiedExtension_form_multiple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : GlobalTheory.UPoinc.UTrait Xo c) (n : ℕ), 0 < n →
    ∃ (T₂ : GlobalTheory.UPoinc.UTrait Xo c) (g : T.V →+* T₂.V) (gK : FractionRing T.V →+* FractionRing T₂.V)
      (e : T.P.D.toPre.X ≃ₗ[𝓞 E] T₂.P.D.toPre.X) (q : ℕ), Function.Injective g ∧ IsLocalHom g ∧
      (∀ a, gK (algebraMap T.V _ a) = algebraMap T₂.V _ (g a)) ∧ T₂.y = spMap gK ≫ T.y ∧ 0 < q ∧
      ∀ a b, T₂.be (e a) (e b) = ((n * q : ℕ) : ℤ) * T.be a b := by
  first | exact @GlobalTheory.UPoinc.uTrait_ramExt | exact GlobalTheory.UPoinc.uTrait_ramExt | (intros; apply GlobalTheory.UPoinc.uTrait_ramExt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical


theorem _root_.GlobalTheory.T.polarisationFunction_mul_ramificationIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (T T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → φ.evalZ T'.be = m * φ.evalZ T.be := by
  first | exact @GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul | exact GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul | (intros; apply GlobalTheory.UPoinc.UTraitRam.evalZ_eq_mul <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.kodaira_spencer_tangent_difference : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  first | exact @GlobalTheory.FlagTan.eq_of_isKS_eq | exact GlobalTheory.FlagTan.eq_of_isKS_eq | (intros; apply GlobalTheory.FlagTan.eq_of_isKS_eq <;> assumption)
end
