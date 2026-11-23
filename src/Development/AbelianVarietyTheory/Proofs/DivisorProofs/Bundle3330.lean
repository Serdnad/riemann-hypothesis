module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle751
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle153
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
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
import Mathlib.RingTheory.DualNumber
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepBC



theorem exists_pelUnif_baseChange_of_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (y : Sp (FractionRing V) ⟶ Xo.XF c) (P : PELUnif (maximalIdeal V) t), GenOf Xo c y t → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁) (fK : FractionRing V →+* FractionRing V₁), IsCN V₁ → Function.Injective ρ → IsLocalHom ρ → (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (ρ a)) → ∃ (t₁ : SAB H (Sp V₁)) (P₁ : PELUnif (maximalIdeal V₁) t₁) (p : IsPullDeg ρ P.D.toPre P₁.D.toPre), GenOf Xo c (spMap fK ≫ y) t₁ ∧ (∀ (a : 𝓞 E) x, p.xe (a • x) = a • p.xe x) ∧ ∀ x r, Formalism.L2.Pj.PsiCoord P.D.toPre (p.xe x) r → ∃ w : V₁ˣ, Formalism.L2.Pj.PsiCoord P₁.D.toPre x (w * ρ r) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV t y P hG V₁ _ _ _ ρ fK hV₁ hρ hl hfK
  have hR : GlobalTheory.Mum.Base V := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  have hR₁ : GlobalTheory.Mum.Base V₁ := ⟨⟨hV₁.1, inferInstance, hV₁.2.1, hV₁.2.2.1⟩, hV₁.2.2.2⟩
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨Wo, hWo, ⟨hψ⟩⟩ := h5.psiOnExists V (maximalIdeal V) hR.1 P.D
  let WS : Set (PrimeSpectrum V) := (Wo : Set (Sp V))
  have hWS : IsOpen WS := Wo.isOpen
  have hbot : (⊥ : PrimeSpectrum V) ∈ WS := by
    have := hWo
    rw [genericPoint_eq_bot_of_affine] at this
    exact this
  obtain ⟨_, ⟨f, rfl⟩, hf, hfW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hbot hWS
  have hf0 : f ≠ 0 := by
    intro e
    apply hf
    rw [e]
    show (0 : V) ∈ (⊥ : PrimeSpectrum V).asIdeal
    exact Ideal.zero_mem _
  have hψW : ∀ x, PsiUnitOn P.D.toPre x (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum V)) := by
    intro x j U hU hUW
    exact GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn V P.D.toPre Wo hψ x j U hU (hUW.trans hfW)
  have hρf : ρ f ≠ 0 := fun e => hf0 (hρ (e.trans (map_zero ρ).symm))
  obtain ⟨t₁, P₁, p, ⟨m₀⟩, hlin, -⟩ := GlobalTheory.LocalPull.exists_pelUnif_pull V V₁ hR hR₁ t P ρ hl f hρf hψW
  refine ⟨t₁, P₁, p, ?_, hlin, fun x r hr => GlobalTheory.PelCoordPull.psiCoord_pull p x r hr⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hG
  have semiPull {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G]
      (h : IsSemiAbelian G) : IsSemiAbelian ((Over.pullback f).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h.comm; infer_instance
    · have := h.smooth; change Smooth (pullback.snd G.hom f); infer_instance
    · have := h.separated; change IsSeparated (pullback.snd G.hom f); infer_instance
    · have := h.quasiCompact; change QuasiCompact (pullback.snd G.hom f); infer_instance
    · have := h.geomConnected; change GeometricallyConnected (pullback.snd G.hom f); infer_instance
    · intro Ω _ _ q
      obtain ⟨e⟩ := h.fibres Ω (q ≫ f)
      exact ⟨torusExtOfIso (pullCompIso q f G) e⟩
  have sabPull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
      ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, semiPull f t.G t.semi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
    have h := isGrpPullback_pullback t.G f
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
        pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
        pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
      Over.OverMorphism.ext (by
        show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP, cub, sym, adj, prim, n, -⟩ := sabPull CubePf.cubePull (jK V₁) t₁
  let tK₁ : SAB H (Sp (FractionRing V₁)) := ⟨(Over.pullback (jK V₁)).obj t₁.G, semiPull _ t₁.G t₁.semi,
    OAct.pullback _ t₁.G t₁.act, PP, cub, sym, adj, prim⟩
  have n' : SABMap tK₁ t₁ (jK V₁) := n
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ t t₁ tK₁ _ _ m₀ n'
  have sq : jK V₁ ≫ spMap ρ = spMap fK ≫ jK V := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact (hfK a).symm
  rw [sq] at b
  obtain ⟨c', -⟩ := sabCancel pullCubCancel E H _ _ _ t tK tK₁ _ _ m₁ b
  obtain ⟨d, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t tK tK₁ _ _ m₂ c'
  refine ⟨tK₁, ⟨n'⟩, ⟨?_⟩⟩
  rw [Category.assoc]
  exact d

end GlobalTheory.USepBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_field_over_trait : ∀ (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F) (_ : Algebra (FractionRing W) F) (_ : Kb R →ₐ[FractionRing R] F), ∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r)) := by
  intro R _ _ W _ _ φ hφ
  let g : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := (IsFractionRing.lift (K := FractionRing R) hg).toAlgebra
  refine ⟨Kb W, inferInstance, inferInstance, inferInstance, inferInstance, IsAlgClosed.lift, fun r => ?_⟩
  exact IsFractionRing.lift_algebraMap hg r

theorem exists_map_exp_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  intro R _ _ _ hR D C j
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  have h1 : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  obtain ⟨wA, hwA⟩ := C.α_lb
  have hL : C.P.L.L.IsLB := by first | exact C.P.L.isLB | exact C.P.L.hL | exact C.P.L.lb
  have hL' : C.A.L.IsLB := C.A.isLB
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  · obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
    obtain ⟨K₀, _, _, _, _, em₀, hK₀⟩ := exists_field_over_trait R W₀ T₀.φ T₀.inj
    obtain ⟨lab, E, hlab, hE, -⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W₀ T₀ K₀ em₀ hK₀
    obtain ⟨Eb, hEb⟩ := GlobalTheory.Mum.Desc.eqv_down R hR D C.A (C.n ^ j) hodd (C.lab j) K₀ em₀ lab E hlab hE
    have hgal := GlobalTheory.Mum.labExt_of_trait R hR D C j W₀ ⟨T₀⟩
    obtain ⟨Φ₀, E₀, hE₀, hΦ₀⟩ := GlobalTheory.Mum.exists_eqv_rational R hR D C.A (C.n ^ j) hodd (C.lab j) Eb hEb hgal
    choose Φ hΦ using fun F₀ => GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L C.A.L C.α wA hL hL' hwA (C.n ^ j) (Φ₀ F₀)
    refine ⟨Φ, fun W _ _ _ T => ?_⟩
    obtain ⟨K, _, _, _, _, em, hK⟩ := exists_field_over_trait R W T.φ T.inj
    obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure R hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W T K em hK
    exact GlobalTheory.T.traitExpansion_descends_from_algClosed_field R hR D C (C.n ^ j) W T K hK Φ c hc (fun F₀ => GlobalTheory.T.exists_integralSection_expanding_thetaFamily R hR D C (C.n ^ j) h1 W T F₀) hcv
  · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LatId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem second_diff_bal {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add (f := _), ← add_smul, hw, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring



theorem lattice_eq_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ' (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ' (hD₁.xe.symm y))) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → ∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ _ hVc f₁ f₂ hf₁ hf₂ lf₁ lf₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b ph hE₁ hE₂
    hM hlin hpairs
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff_bal Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  obtain ⟨ββ₁, w₁, hF₁⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl

  have hcong : ∀ y, ∃ z, ga y = y + l.M' • z := by
    intro y
    obtain ⟨p₀, hp₀y, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) (e y)
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpairs p₀
    rw [hp₀y, AddEquiv.symm_apply_apply] at hy₁ hy₂
    have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(hD₂.xe z), ?_⟩
    rw [smul_neg, hga, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h.symm

  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM
  let gz : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv
  have hgz : ∀ y, gz (e y) = e (ga y) := fun y => by
    show e (ga (e.symm (e y))) = e (ga y)
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    gz (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hform : ∀ y z, ∑ i, (d₂ i : ℤ) * C.δ i (ga y) (ga z) = ∑ i, (d₁ i : ℤ) * C.δ i y z := by
    intro y z
    have h := LinearMap.congr_fun₂ hsum (e y) (e z)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, hgz, nsmul_eq_mul] at h
    simp only [hδ]
    exact h.symm
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, C.δ i y y := by
    intro y hy
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy
    have hi' : 0 < C.δ i y y :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast (by omega : 0 < l.M'))).1 hi
    exact Finset.sum_pos' (fun j _ => C.cone.nonneg j y) ⟨i, Finset.mem_univ _, hi'⟩
  have hid := GlobalTheory.UCanon.eq_self_of_cone_congMod H φ (min Dw.p Dw.q) hφ hns C.P.D.toPre.X C.rank C.m C.δ C.cone hpos ga
    d₂ d₁ hd₂ hd₁ hform l.M' hn hcong
  intro y
  exact hid y

end GlobalTheory.UCanon.LatId
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → (∀ i, s i ≠ 0) → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a : Fin T.r → ℤ), ∃ p : QkPt D F n, p.y = e.symm a ∧ TautPt T ω s ε n D e β ββ w F a p.g := by
  first | exact @GlobalTheory.TInj.exists_qkPt_tautPt | exact GlobalTheory.TInj.exists_qkPt_tautPt | (intros; apply GlobalTheory.TInj.exists_qkPt_tautPt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  first | exact @GlobalTheory.TInj.pull_unif_tors | exact GlobalTheory.TInj.pull_unif_tors | (intros; apply GlobalTheory.TInj.pull_unif_tors <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.Rigid

theorem isLocalHom_of_fst {R : Type} [CommRing R] [IsLocalRing R] {k : Type} [Field k] (θ : R →+* DualNumber k)
    (h : ∀ r ∈ maximalIdeal R, (θ r).fst = 0) : IsLocalHom θ := by
  refine ⟨fun r hr => ?_⟩
  by_contra hn
  have hm : r ∈ maximalIdeal R := (mem_maximalIdeal r).mpr hn
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, h r hm] at hr
  exact not_isUnit_zero hr

end GlobalTheory.UCanon.Rigid

theorem GlobalTheory.UCanon.isRigid_canon : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hB C Cn k _ ρ a hmax hs hc
  have hbase := GlobalTheory.T.base_rigidity_tangent_vector_constant Xo c φ R hB C Cn k ρ a hc
  have htor := GlobalTheory.T.torus_rigidity_snd_eq_zero_canonicalChart Xo c φ R hB C Cn k ρ a hc hbase
  have h₁ : IsLocalHom ρ := GlobalTheory.UCanon.Rigid.isLocalHom_of_fst ρ hmax
  have h₂ : IsLocalHom (GlobalTheory.RigChart.constHom ρ) := by
    refine GlobalTheory.UCanon.Rigid.isLocalHom_of_fst _ fun r hr => ?_
    simp [GlobalTheory.RigChart.constHom, hmax r hr]
  have hψ : ρ.comp Cn.ψ = (GlobalTheory.RigChart.constHom ρ).comp Cn.ψ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      have := congrArg (fun f => f x) hbase
      simpa [GlobalTheory.RigChart.constHom] using this
    · rintro (i | j)
      · simp [GlobalTheory.RigChart.constHom, Cn.bd, hs]
      · apply TrivSqZeroExt.ext
        · simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
        · simpa [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl] using htor j
  have heq := GlobalTheory.TChart.cuniq _ R (DualNumber k) Cn.ψ Cn.compl ρ (GlobalTheory.RigChart.constHom ρ) h₁ h₂ hψ
  intro r
  rw [heq]
  simp [GlobalTheory.RigChart.constHom, TrivSqZeroExt.algebraMap_eq_inl]
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem intCast_comp_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    (n : End A).asHom ≫ u = n • u := by
  rw [← zsmul_one]
  change (n • 𝟙 A) ≫ u = n • u
  rw [Preadditive.zsmul_comp, Category.id_comp]

theorem comp_intCast_cpisog {K : Type} [Field K] {A B : AbVar K} (n : ℤ) (u : A ⟶ B) :
    u ≫ (n : End B).asHom = n • u := by
  rw [← zsmul_one]
  change u ≫ (n • 𝟙 B) = n • u
  rw [Preadditive.comp_zsmul, Category.comp_id]

theorem charpoly_eq_of_isogeny_intertwines :
    ∀ (K : Type) [Field K] (A B : AbVar K) (u : A ⟶ B) (f : End A) (g : End B),
      IsIsogeny u → f.asHom ≫ u = u ≫ g.asHom → charpoly f = charpoly g := by
  intro K _ A B u f g hu hfg
  obtain ⟨hdim, -, hpos, -⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B u hu
  have key : ∀ n : ℤ, deg ((n : End A) - f).asHom = deg ((n : End B) - g).asHom := by
    intro n
    have hc : ((n : End A) - f).asHom ≫ u = u ≫ ((n : End B) - g).asHom := by
      rw [End.sub_asHom, End.sub_asHom, Preadditive.sub_comp, Preadditive.comp_sub,
        intCast_comp_cpisog, comp_intCast_cpisog]
      exact congrArg (n • u - ·) hfg
    have h1 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A A B
      ((n : End A) - f).asHom u rfl hdim).2
    have h2 := (GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp K A B B
      u ((n : End B) - g).asHom hdim rfl).2
    rw [hc, h2, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have hg : IsCharpoly g (charpoly f) := ⟨hm, by rw [hd, hdim], fun n => by rw [hev n, key n]⟩
  exact (GlobalTheory.T.abelianVarietyEndCharpoly_spec K B g).2 _ hg

end GlobalTheory.AV.AbVar
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.heatOperator_defect_polynomial_monomial_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∃ (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_polynomial | exact GlobalTheory.HeatDefect.defect_polynomial | (intros; apply GlobalTheory.HeatDefect.defect_polynomial <;> assumption)
end
