module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle044
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle871
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle578
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle824
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle953
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle883
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle916
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle789
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false



noncomputable section

namespace GlobalTheory.GalEqCls

theorem isThClsD_transfer {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {n : ℕ}
    {d d' : Formalism.L2.Pj.DeltaDat Xo c n} (hd : d' = d)
    {Cl Cl' : Type} [Fintype Cl] [Fintype Cl'] (e : Cl ≃ Cl')
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (w' : Cl' → (Fin n → LevQ Dw d'.l₂) → c.F)
    (hw : ∀ k, HEq (w k) (w' (e k)))
    (La : Cl → GenLat E n) (La' : Cl' → GenLat E n) (hLa : ∀ k, La' (e k) = La k)
    (Nc : Cl → ℕ) (Nc' : Cl' → ℕ) (hNc : ∀ k, Nc' (e k) = Nc k)
    (gam : Cl → ℕ) (gam' : Cl' → ℕ) (hgam : ∀ k, gam' (e k) = gam k)
    (vol : c.F) (ep : Cl → c.F) (ep' : Cl' → c.F) (hep : ∀ k, ep' (e k) = ep k)
    {Vs : Type} [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (x : Cl → Vs) (x' : Cl' → Vs) (hx : ∀ k, x' (e k) = x k) (f : Rul Xo c)
    (h : IsThClsD Xo c d w La Nc gam vol ep io x f) : IsThClsD Xo c d' w' La' Nc' gam' vol ep' io x' f := by
  subst hd
  intro k _ _ A A₂ hk y y₂ hy
  obtain ⟨vc, hvc, he⟩ := @h k _ _ A A₂ hk y y₂ hy
  refine ⟨fun cl => vc (e.symm cl), fun cl => ?_, ?_⟩
  · obtain ⟨k', rfl⟩ := e.surjective cl
    dsimp only
    rw [e.symm_apply_apply, ← eq_of_heq (hw k'), hLa, hNc, hx]
    exact hvc k'
  · rw [he]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k' _ => ?_
    dsimp only
    rw [e.symm_apply_apply, hgam, hep]

theorem galRul_isSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ (hf : Fixes M.c' ta) (k0 : ℂ), IsRoot1 k0 ∧ ∀ (a b : Tp) (e : M.Cl' a ≃ M.Cl' b), SameCover M a b e → ConjTup R τ (tup a) (tup b) → ∃ (u : M.c'.F) (s : (AE D)ˣ), (u : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (xs : M.Cl' a → VsV D i M.c'.F) (xs' : M.Cl' b → VsV D i M.c'.F), (∀ k, (xs' (e k) : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (xs k : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M a xs f → u • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M b xs' (u • galRul hf f) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hf : Fixes M.c' ta := ⟨fun φ x => Subtype.ext (by rw [hta]; exact hfix.host φ x),
    fun a => Subtype.ext (by rw [hta]; exact hfix.core ⟨a, T.Q.c.le a.2⟩)⟩
  obtain ⟨k0, hk0, hcxi⟩ := GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix hcurve hxi
  have hk0ne : k0 ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn, hkn⟩ := hk0
    rw [zero_pow hn.ne'] at hkn
    exact zero_ne_one hkn
  refine ⟨hf, k0⁻¹, ?_, ?_⟩
  · obtain ⟨n, hn, hkn⟩ := hk0
    exact ⟨n, hn, by rw [inv_pow, hkn, inv_one]⟩
  intro a b e hsame hconj
  obtain ⟨⟨cx, hcx⟩, hU, hdict, -, -, hcl⟩ := id hsame
  obtain ⟨h₂, ka, s1, hka, hev⟩ := hcxi a b cx hcx hU hdict hconj
  obtain ⟨u, s2, w', hu, hw'eq, hw⟩ :=
    GlobalTheory.T.conj_fourierCoefficients_conjugate_tuples D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  obtain ⟨hvol, hep⟩ := GlobalTheory.T.galoisConj_classScalars_and_volume D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix a b e hsame hconj
  have hkane : ka ≠ 0 := fun h0 => by
    have h1 : ((ka : ℂ)) = 0 := by rw [h0]; rfl
    rw [hka] at h1
    exact mul_ne_zero hk0ne (Circle.coe_ne_zero _) h1
  have hune : u ≠ 0 := fun h0 => by
    have h1 : ((u : ℂ)) = 0 := by rw [h0]; rfl
    rw [hu] at h1
    exact Circle.coe_ne_zero _ h1
  refine ⟨(ka * u)⁻¹, (s1 * s2)⁻¹, ?_, ?_⟩
  · have e1 : (((ka * u)⁻¹ : M.c'.F) : ℂ) = ((ka : ℂ) * (u : ℂ))⁻¹ := by push_cast; rfl
    rw [e1, hka, hu, map_inv, map_mul, Circle.coe_inv, Circle.coe_mul]
    ring
  intro xs xs' hxs f hfs hsum
  obtain ⟨-, cga, hio⟩ := hP.io
  have hio' := fun v => GlobalTheory.HarmBasis.mem_HHa_of_mem_span subset_rfl (hio.2.2.1 ▸ LinearMap.mem_range_self M.io v)
  obtain ⟨hLev, -, hN⟩ := hP.cov a
  have hδ := hLev.2.2.2.2.2.2.2.1
  have key := GlobalTheory.GalTw.isThClsD_galRul hC _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf (Vc D i).rank (M.dδ a) h₂ hN hδ cx
    ka u hkane hune hev (M.Cl' a) (M.w a) w' (M.La a) (M.Nc a) (M.gam a) (M.vol a) (M.ep a) (VsV D i M.c'.F) M.io
    (wtA (κ i)) hio' hw xs (fun k => xs' (e k))
    (fun k => GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore hFW i Tp tup M hP τ ta hta hfix (xs k) (xs' (e k)) (hxs k))
    (Vc D i).rank f hfs hsum
  refine ⟨key.1, ?_⟩
  have key2 := key.2
  rw [hvol] at key2
  exact isThClsD_transfer hcx e w' (M.w b) hw'eq (M.La a) (M.La b) (fun k => (hcl k).2.1) (M.Nc a) (M.Nc b)
    (fun k => (hcl k).2.2.1) (M.gam a) (M.gam b) (fun k => (hcl k).2.2.2) (M.vol b) (fun k => ta (M.ep a k)) (M.ep b)
    (fun k => (hep k).symm) M.io (fun k => xs' (e k)) xs' (fun _ => rfl) _ key2

end GlobalTheory.GalEqCls
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem transl_mem_span_gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : φ ∈ Submodule.span ℂ (Gen R i t)) :
    R.ωP i t (1, g) φ ∈ Submodule.span ℂ (Gen R i t) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', f', hf', rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', f', hf', ?_⟩
    have hm : ((1, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (1, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [← hm, map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem finLike_of_likeOff_empty (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : LikeOff R i t ∅ f) : FinLike R i t f :=
  ⟨hf.1, fun c hc h0 => hf.2 c (fun u hu => ⟨hc u hu, fun v hv => absurd hv (Finset.notMem_empty v)⟩) h0⟩

theorem mem_span_gen_of_step (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hst : ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb →
      ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)))
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (Gen R i t) := by
  classical
  induction Sb using Finset.induction_on with
  | empty =>
    intro f _ _ hL
    refine Submodule.subset_span ⟨1, f, finLike_of_likeOff_empty R i t hL, ?_⟩
    have h1 : ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 := rfl
    rw [h1, map_one, Module.End.one_apply]
  | insert v s hv ih =>
    intro f hT hC hL
    have h := hst (insert v s) v (Finset.mem_insert_self v s) f hT hC hL
    rw [dropPl_insert hv] at h
    refine (Submodule.span_le.2 ?_) h
    rintro φ ⟨g, f', hT', hC', hL', rfl⟩
    exact transl_mem_span_gen R i t g (ih f' hT' hC' hL')

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem gen_of_type_clean : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hT hC
  obtain ⟨Sb, hL⟩ := GlobalTheory.T.exists_places_thetaFunction_fixedVectorShape D G Pl0 T A Ks R F hG hP i t f hT.1
  refine mem_span_gen_of_step R i t ?_ Sb f ⟨hT.1, fun κ hκ _ => hT.2 κ hκ⟩
    (fun PP a ha tr ε hε _ κ hκ _ => hC PP a ha tr ε hε κ hκ) hL
  intro Sb v hv f hT hC hL
  by_cases hpg : ∃ PP ∈ R.Pg, Over PP v
  · exact GlobalTheory.T.local_generation_thetaFun_at_type_prime D G Pl0 T A Ks R F hG hP i t Sb v hv hpg f hT hC hL
  by_cases hq : ∃ PP ∈ R.Q t, Over PP v
  · exact GlobalTheory.T.localGeneration_thetaFunctions_twistPlace D G Pl0 T A Ks R F hG hP i t Sb v hv (fun PP h ho => hpg ⟨PP, h, ho⟩) hq f hT hC hL
  have hoff : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ Over PP v := by
    rintro PP (h | h) ho
    · exact hpg ⟨PP, h, ho⟩
    · exact hq ⟨PP, h, ho⟩
  by_cases hs : ∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · exact GlobalTheory.T.thetaFunction_localGeneration_splitPlaceOffLevels D G Pl0 T A Ks R F hG hP i t Sb v hv hs hoff f hT hC hL
  · refine GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel hH D G Pl0 T A Ks R F hG hP i t Sb v hv ?_ hoff f hT hC hL
    intro ε hε e he
    by_contra hne
    exact hs ⟨ε, e, hε, he, hne⟩

end GlobalTheory.DownLift.GenFinite
end
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.card_divisionPoints_half_split_place_norm_pow : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ N : ℕ, 0 < N → Nat.card (GlobalTheory.DivPtFourier.DQ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) e N) = Ideal.absNorm (P.maxPowDividing (Ideal.span {((N : ℕ) : 𝓞 D.host.E)})) ^ (S.rank * T.rank) := by
  first | exact @GlobalTheory.DivPtLocal.natCard_DQ | exact GlobalTheory.DivPtLocal.natCard_DQ | (intros; apply GlobalTheory.DivPtLocal.natCard_DQ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefTheta

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame GlobalTheory.ThetaTri
open scoped TensorProduct

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem reference_tuple_used (D : D7) : Used0 D D.what₂.mu0 := Or.inl rfl

abbrev t0 (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : T := Y.tupT D.what₂.mu0

def repY (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : D.what₂.FT → NG.FinTyp D.host.E D.R.r :=
  fun σ => rowRepR R.θ (Y.eFT σ)

def IsCanonR (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (i : Fin D.R.m) {j : ℕ} (hj : i.1 + 1 = j) (X : GlobalTheory.NPin.RowMod D rep j) : Prop :=
  ∃ (e : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A))) (c : ℝ), Function.Injective e ∧ 0 < c ∧
    X.C.map e = Minf R.θ (Y.PW i) (R.MW i (sg0 D A3.A)) ∧
    (∀ h x, e (X.ρ h x) = actM (Y.PW i) (R.MW i (sg0 D A3.A)) h (e x)) ∧
    (∀ x ∈ X.C, ∀ y ∈ X.C, X.B x y = (c : ℂ) * Mult.ipM (R.MW i (sg0 D A3.A)) (R.νW i) (R.fdW i) (e x) (e y)) ∧
    ∀ y : D.what₂.Mj (i.1 + 1), PiTensorProduct.lift (e (X.φ (hj ▸ y))) = (Y.IL.jMj i y).1

variable {Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

def eC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : X.A →ₗ[ℂ] Mult.MMap (R.MW i (sg0 D A3.A)) :=
  Classical.choose hc

def cC {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) : ℝ :=
  Classical.choose (Classical.choose_spec hc)

def yv {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {i : Fin D.R.m} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥X.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D i) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A3.A)) τ).subtype)
      (kUnit (R.MW i (sg0 D A3.A)))) ∘ₗ
    (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ eC hc ∘ₗ X.C.subtype

variable {M : MtFam D}

def fV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) :
    ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ]
      (Formalism.L2.Theta.GA D (Vc D i) → (R.cV i).W) :=
  (R.cV i).ext ∘ₗ
    { toFun := fun F k => Ad.eW D.what₂.mu0 (reference_tuple_used D) i
        ((F : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }

def omStd (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (t : T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
  (R.ωP i t).comp ((Ad.PV i).ψ.prodMap (Y.PW i).ψ)

def Om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    Submodule ℂ ((R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) :=
  OmSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def om (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(Om Ad i hc) :=
  omSub (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) R.ψ (omStd Ad i (t0 Y))

def lamV (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) (φ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y : ↥X.C) : ℂ :=
  GlobalTheory.ThetaTri.lamV (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) φ Fm y

def lamL (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} {j : ℕ} {hj : i.1 + 1 = j}
    {X : GlobalTheory.NPin.RowMod D rep j} (hc : IsCanonR Y i hj X) :
    ↥(Om Ad i hc) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ :=
  lam (R.ωP i (t0 Y)) (fV Ad i) (yv hc) (R.νV i (t0 Y)) (R.fdV i (t0 Y)) (R.νW i) (R.fdW i) (cC hc : ℂ) R.ψ
    (omStd Ad i (t0 Y))


variable (Y) in
def phi0 (i : Fin D.R.m) : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A3.A))) (R.BV i)
    (onb (R.MW i (sg0 D A3.A))) (R.vP i (t0 Y)) ∘ₗ R.ioP i (kUnit (R.MW i (sg0 D A3.A)))

end GlobalTheory.RefTheta

end
end
