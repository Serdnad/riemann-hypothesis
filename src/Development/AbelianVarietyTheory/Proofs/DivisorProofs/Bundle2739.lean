module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle650
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle289
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickActionsIsomorphic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle634
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.HorConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_matrix {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {m n : ℕ} (h : m = n)
    {v v' : Fin n → (epsAt x ⟶ t.G)} {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k)
    (hv' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v' i).left = u' k)
    {M : Matrix (Fin m) (Fin m) R} (hM : ∀ i, IsCombAtG t x u (M i) (u' i)) :
    ∃ M' : Matrix (Fin n) (Fin n) R, M'.det = M.det ∧ ∀ i, IsCombAt x (M' i) v (v' i) := by
  subst h
  refine ⟨M, rfl, fun i => (EigParts.comb_iff v _ _).2 ?_⟩
  rw [hv' i i rfl, show (fun i => (v i).left) = u from funext fun i => hv i i rfl]
  exact hM i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}


open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq in
theorem exists_matrix_det_ne {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Y.X} (f₁ f₂ : EigFrame Y φ x)
    (ρ : E →+* ℂ) : ∃ M : Matrix (Fin (D.mult ρ)) (Fin (D.mult ρ)) k,
      (∀ i, IsCombAtG Y.t x (f₁.v ρ) (M i) (f₂.v ρ i)) ∧ M.det ≠ 0 := by
  obtain ⟨n, xc, hx⟩ := exists_chart Y.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan ρ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan ρ i)
  choose M hM using fun i => (f₁.basis ρ _ (f₂.tan ρ i) (f₂.eig ρ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v ρ = fun j => vec Y.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  have hind : ∀ a : Fin (D.mult ρ) → k, ∑ i, a i • e₂ i = 0 → a = 0 := fun a ha => by
    have hb := f₂.basis ρ _ (vec_tan hx 0) ((vec_eig_iff hx _ _).2 (Submodule.zero_mem _))
    rw [show f₂.v ρ = fun j => vec Y.t _ xc (e₂ j) from funext he₂] at hb
    exact hb.unique ((comb_iff hx _ _ _).2 ha.symm) ((comb_iff hx _ _ _).2 (by simp))
  refine ⟨Matrix.of M, hM, fun h0 => ?_⟩
  obtain ⟨a, ha, ha0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine ha (hind a ?_)
  simp only [hM', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.sum_smul]
  have : ∑ i, a i * M i j = 0 := congrFun ha0 j
  rw [this, zero_smul]

theorem quot_eq {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {e : c.F →+* ℂ} {h : CxFr Y e → ℂ} (hh : HorFn τ h)
    {V : Set (gen Y)} {σb : RuleY Y} (hσ : SecY Y V τ σb) (a a' : CxFr Y e) (ha : a.1.1 = a'.1.1) (hi : Inner a.1)
    {v w v' w'} (hf : FrY Y V τ e a.1.1 v w) (hm : Match τ a.2 v w) (hf' : FrY Y V τ e a'.1.1 v' w')
    (hm' : Match τ a'.2 v' w') : σb ℂ a.1.1 v w * (h a)⁻¹ = σb ℂ a'.1.1 v' w' * (h a')⁻¹ := by
  obtain ⟨x, f⟩ := a
  obtain ⟨x', f'⟩ := a'
  obtain rfl : x = x' := Subtype.ext ha
  obtain ⟨M, hM, hM0⟩ := exists_matrix_det_ne f f' τ
  obtain ⟨N, hN, -⟩ := exists_matrix_det_ne f f' (conjEmb τ)
  obtain ⟨M', eM, hM'⟩ := exists_matrix (GlobalTheory.Harm.mult_of_mem D hτ) hm.1 hm'.1 hM
  obtain ⟨N', eN, hN'⟩ := exists_matrix (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) hm.2 hm'.2 hN
  have e₁ := hσ.2 ℂ e x.1 v w v' w' M' N' hf hf' hM' hN'
  have e₂ := hh.2.1 ⟨x, f⟩ ⟨x, f'⟩ M N hi ⟨rfl, hM⟩ ⟨rfl, hN⟩
  have h₁ := hh.1 ⟨x, f⟩ hi
  have h₂ := hh.1 ⟨x, f'⟩ hi
  rw [eM, eN] at e₁
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂]
  refine mul_right_cancel₀ hM0 ?_
  linear_combination σb ℂ x.1 v w * e₂ + h ⟨x, f⟩ * e₁


open GlobalTheory.CxPts GlobalTheory.ShFam.Hor.Sec in
theorem exists_const_mul_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hstr hτ hh σb hσ
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hstr
  choose v₀ w₀ hf₀ hm₀ using fun y => (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) _ (hφ y)
    (by rintro _ ⟨z, rfl⟩; rw [← hV, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩) (fr y)).1
  let s (y : B.X) : Γ(B.X, W y) := σb _ _ (v₀ y) (w₀ y)
  have key (y) (p : GlobalTheory.CxPts B.str e) (hp : p ∈ ptsIn B.str e (W y)) :
      ∃ v w, FrY Y V τ e (a y p).1.1 v w ∧ Match τ (a y p).2 v w ∧ σb ℂ (a y p).1.1 v w = ev B.str e _ (s y) p := by
    have hx : (a y p).1.1 = spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io := by
      have : spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) = p.1 :=
        GlobalTheory.Points.specMap_valMap_fromSpec (hW y) p.1 hp
      rw [ha, ← Category.assoc, this]
    obtain ⟨v, w, h₁, h₂, h₃⟩ := exists_pull (evHom hp) (hf₀ y) hx
    have hj : (evHom hp).comp (φ y) = e :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective (h₁.1.symm.trans (a y p).1.2))
    refine ⟨v, w, by have := h₁; rwa [hj] at this, ⟨fun i k hik => ?_, fun i k hik => ?_⟩, ?_⟩
    · rw [h₂, (hm₀ y).1 i k hik, hv y p hp]
    · rw [h₃, (hm₀ y).2 i k hik, hv y p hp]
    · rw [ev_eq hp]
      exact hσ.1 _ ℂ (evHom hp) (Chart.dualMapR (evHom hp)) _ _ _ _ _ _ v w
        (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
        (by ext <;> simp [Chart.dualMapR]) (hf₀ y) h₁ hx h₂ h₃
  have hA : Dense (ptsIn B.str e (io ⁻¹ᵁ (genBd Y).compl)) := by
    refine (GlobalTheory.T.complexPoints_nonempty_dense_variety c.F B e).2 _ ?_
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨z, fun hb => hb hz⟩
  let R := AnRead.all B.str e B.dim
  choose u hu he using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  let pt (z : GlobalTheory.CxPts B.str e) : B.X := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : GlobalTheory.CxPts B.str e) : z ∈ ptsIn B.str e (W (pt z)) := mem_ptsIn.2 (hy _)
  obtain ⟨q, hq, hqe⟩ := exists_holoOn_of_local (R := R) hA (S := Set.univ)
    (u := fun z => ev B.str e _ (s (pt z)) z * (h (a (pt z) z))⁻¹) fun y _ =>
    ⟨ptsIn B.str e (W (pt y)), fun z => ev B.str e _ (s (pt y)) z * u (pt y) z, isOpen_ptsIn _, hpt y,
      (R.holoOn_ev _ _).mul (hu _), fun z hz => by
        obtain ⟨v, w, h₁, h₂, h₃⟩ := key _ z hz.1
        obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
        have := quot_eq hτ hh hσ _ _ ((ha _ _).trans (ha _ _).symm) ((inner_iff (ha _ z)).2 hz.2) h₁ h₂ h₁' h₂'
        rw [h₃, h₃'] at this
        simp only [he _ hz]
        exact this⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.ConstFn.holoOn_univ_const c.F B e R q hq
  refine ⟨κ, fun b v w hi hb hm => ?_⟩
  have hr : Set.range b.1.1 ⊆ Set.range io := hV ▸ hb.2.1
  have hl : IsOpenImmersion.lift io b.1.1 hr ≫ io = b.1.1 := IsOpenImmersion.lift_fac _ _ _
  let z : GlobalTheory.CxPts B.str e := ⟨IsOpenImmersion.lift io b.1.1 hr, by rw [← hstr, ← Category.assoc, hl]; exact b.1.2⟩
  obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
  have e₁ := quot_eq hτ hh hσ b _ (hl.symm.trans (ha _ z).symm) hi hb hm h₁' h₂'
  have e₂ := hqe (x := z) ⟨trivial, (inner_iff hl.symm).1 hi⟩
  rw [hκ] at e₂
  rw [h₃'] at e₁
  rw [e₂]
  exact (mul_inv_eq_iff_eq_mul₀ (hh.1 b hi)).1 e₁

end GlobalTheory.DetLine.HorConst
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartOpen

theorem isOpenImmersion_of_stalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f]
    (h : ∀ x : X, ∃ s : Spec (Y.presheaf.stalk (f x)) ⟶ X, s ≫ f = Y.fromSpecStalk (f x)) :
    IsOpenImmersion f := by
  have hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom := by
    intro x
    refine ⟨?_, f.stalkMap_surjective x⟩
    obtain ⟨s, hs⟩ := h x
    obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s
    rw [SpecToEquivOfLocalRing_symm_apply] at hs
    dsimp only at hs
    have h1 : f x' = f x := by
      have := Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)
      rw [hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint] at this
      exact this.symm
    have hx : x' = x := f.isClosedEmbedding.injective h1
    subst hx
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
    have key : f.stalkMap x' ≫ φ = 𝟙 _ := by
      have e := (SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective
        (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩)
        (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
            dsimp only
            rw [hs, Spec.map_id, Category.id_comp])
      rw [SpecToEquivOfLocalRing_eq_iff] at e
      obtain ⟨_, e⟩ := e
      simpa using e
    intro a b hab
    have := congrArg φ.hom hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at this
  have : Flat f := (Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)
  exact IsOpenImmersion.of_flat_of_mono f

theorem residue_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    ∃ s : Spec (Y.residueField (f x)) ⟶ X, s ≫ f = Y.fromSpecResidueField (f x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨IsLocalRing.residue _ c, rfl⟩
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI := P'.fin.finite
  exact inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

theorem free_Bt : Module.Free O (Bt P' x0 hu) := by
  haveI := P'.fin.free
  exact inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

end

theorem isOpenImmersion_jH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h
  set j := jH P' x0 hu hg.1 h
  haveI := P.semi.separated
  haveI := P.semi.smooth
  have hm : Mono j.left := by
    haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1
    have e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left := by
      rw [← Over.comp_left, jH_ι]
    exact mono_of_mono_fac e
  have H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left := by
    have h := (IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)
    have h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))
    exact h' ▸ h
  have : LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h3 := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom
  have : IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h4 := IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom
  have hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3
  have hZsep : IsSeparated (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4
  haveI := finite_Bt P' x0 hu
  haveI := free_Bt P' x0 hu
  have hHfin : IsFinite (Hs P' x0 hu).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _
    exact RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)
  have hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom := Over.w j
  have : IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHfin
  have : LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHlfp
  have : IsFinite j.left := IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom
  have : IsClosedImmersion j.left := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩
  have : LocallyOfFinitePresentation j.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom
  refine isOpenImmersion_of_stalk j.left fun x => ?_
  obtain ⟨s, hs⟩ := residue_lift j.left x
  haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) :=
    LocallyRingedSpace.isLocalRing _ _
  exact GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this)
    ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩

end GlobalTheory.FinPartOpen
end
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

set_option autoImplicit false

noncomputable section

open GlobalTheory.HeatTrans

namespace GlobalTheory.Heat

theorem IsInv.pbT_tr_preimage {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G)
    (O : G.left.Opens) (f : Γ(G.left, O)) :
    dd (tr G x ⁻¹ᵁ O) (pbT (tr G x) f (tr G x ⁻¹ᵁ O)) = pbT (tr G x) (dd O f) (tr G x ⁻¹ᵁ O) := by
  set T := tr G x with hTdef
  have key : ∀ (U : G.left.Opens) (hU : IsAffineOpen U) (hle : U ≤ T ⁻¹ᵁ O),
      (G.left.presheaf.map (homOfLE hle).op).hom (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) =
        (G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O)) := by
    intro U hU hle
    let g : Sp Γ(G.left, U) ⟶ G.left := hU.fromSpec
    let φ : R →+* Γ(G.left, U) := (Spec.preimage (g ≫ G.hom)).hom
    have hφ : g ≫ G.hom = spMap φ := by simp [φ, spMap]
    have hgU : ⊤ ≤ g ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have hgO : ⊤ ≤ g ⁻¹ᵁ (T ⁻¹ᵁ O) := hgU.trans (g.preimage_mono hle)
    have hgTO : ⊤ ≤ (g ≫ T) ⁻¹ᵁ O := hgO
    have e : (dualMap φ).comp (algebraMap R (DualNumber R)) =
        (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))).comp φ := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    have hv : (tv v).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
      (Over.w (tv v)).trans (Category.comp_id _)
    have h2 : (spMap (dualMap φ) ≫ (tv v).left) ≫ G.hom = (tEpsG (g ≫ G.hom)).hom := by
      show _ = spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g ≫ G.hom
      refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
      rw [hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
    let g' : tEpsG (g ≫ G.hom) ⟶ G :=
      Over.homMk (spMap (algebraMap Γ(G.left, U) (DualNumber Γ(G.left, U))) ≫ g) (Category.assoc _ _ _)
    let v' : tEpsG (g ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv v).left) h2
    have htr : IsTr G φ g v (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩
    have hval := hinv.2 _ φ g _ (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O)) hφ hgO htr

    have hT' : (g ≫ T) ≫ G.hom = g ≫ G.hom := by rw [Category.assoc, hTdef, tr_hom]
    have hφ₁ : (g ≫ T) ≫ G.hom = spMap φ := hT'.trans hφ
    have eo : tEpsG ((g ≫ T) ≫ G.hom) = tEpsG (g ≫ G.hom) := congrArg tEpsG hT'
    let g'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ (g' * (toUnit _ ≫ x))
    let v'₁ : tEpsG ((g ≫ T) ≫ G.hom) ⟶ G := eqToHom eo ≫ v'
    have hl : ∀ k : tEpsG (g ≫ G.hom) ⟶ G, (eqToHom eo ≫ k).left = k.left := by
      intro k; rw [Over.comp_left]; simp
    have hg'T : g' ≫ (𝟙 G * (toUnit G ≫ x)) = g' * (toUnit _ ≫ x) := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (g' ≫ toUnit G) (toUnit _)]
    have hwT : (g' * v') ≫ (𝟙 G * (toUnit G ≫ x)) = (g' * (toUnit _ ≫ x)) * v' := by
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique ((g' * v') ≫ toUnit G) (toUnit _), _root_.mul_assoc, _root_.mul_comm v',
        ← _root_.mul_assoc]
    have htr₁ : IsTr G φ (g ≫ T) v ((g' * v').left ≫ T) := by
      refine ⟨g'₁, v'₁, ?_, ?_, ?_⟩
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x))).left = _
        rw [hl, ← hg'T, Over.comp_left]
        rfl
      · show (eqToHom eo ≫ v').left = _
        rw [hl]
        rfl
      · show (eqToHom eo ≫ (g' * (toUnit _ ≫ x)) * (eqToHom eo ≫ v')).left = _
        rw [← MonObj.comp_mul, hl, ← hwT, Over.comp_left]
        rfl
    have hval₁ := hinv.2 _ φ (g ≫ T) _ O f hφ₁ hgTO htr₁

    have hpb : ∀ s : Γ(G.left, O), pbT T s (T ⁻¹ᵁ O) = (T.app O).hom s := fun s => by
      rw [GlobalTheory.KS.pbT_of_le T le_rfl, Scheme.Hom.app_eq_appLE]
    have hL : valR g (T ⁻¹ᵁ O) (dd (T ⁻¹ᵁ O) (pbT T f (T ⁻¹ᵁ O))) = valR (g ≫ T) O (dd O f) := by
      rw [← hval, ← hval₁, GlobalTheory.HolHom.valR_comp, hpb]
    have hR : valR g (T ⁻¹ᵁ O) (pbT T (dd O f) (T ⁻¹ᵁ O)) = valR (g ≫ T) O (dd O f) := by
      rw [GlobalTheory.HolHom.valR_comp, hpb]
    rw [← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom _),
      ← GlobalTheory.DetRatio.valR_fromSpec hU ((G.left.presheaf.map (homOfLE hle).op).hom (pbT T (dd O f) (T ⁻¹ᵁ O))),
      GlobalTheory.HolHom.valR_res g hle _ hgU, GlobalTheory.HolHom.valR_res g hle _ hgU]
    exact hL.trans hR.symm
  refine G.left.sheaf.eq_of_locally_eq' (fun k : {U : G.left.Opens // IsAffineOpen U ∧ U ≤ T ⁻¹ᵁ O} => k.1) _
    (fun k => homOfLE k.2.2) ?_ _ _ fun k => ?_
  · intro y hy
    obtain ⟨U, hU, hyU, hUO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hyU⟩
  · exact key k.1 k.2.1 k.2.2

theorem IsInv.pbT_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G)
    (dd : Fld G.left) (hinv : IsInv G v dd) (x : 𝟙_ (Over (Sp R)) ⟶ G) (O O' : G.left.Opens)
    (hO' : O' ≤ tr G x ⁻¹ᵁ O) (f : Γ(G.left, O)) :
    dd O' (pbT (tr G x) f O') = pbT (tr G x) (dd O f) O' := by
  rw [← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' f, ← GlobalTheory.KS.rsT_pbT (tr G x) le_rfl hO' (dd O f),
    GlobalTheory.KS.rsT_of_le hO', GlobalTheory.KS.rsT_of_le hO', hinv.1.2.2 _ _ hO' le_top,
    IsInv.pbT_tr_preimage G v dd hinv x O f]

end GlobalTheory.Heat
end
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
noncomputable section
namespace GlobalTheory.LocRegFlat

theorem germ_flat {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.Flat := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

theorem chartHom_flat_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx he mm hmm hmem
  have key : GlobalTheory.LocReg.chartHom Y U ξ hx = ((Y.X.presheaf.germ U.1 (genι Y (ξ (closedPoint _))) hx ≫
      (genι Y).stalkMap (ξ (closedPoint _))) ≫ Scheme.stalkClosedPointTo ξ).hom := by
    have h := (genι Y).germ_stalkMap U.1 (ξ (closedPoint _)) hx
    unfold GlobalTheory.LocReg.chartHom
    rw [h]; rfl
  rw [key]
  simp only [CommRingCat.hom_comp]
  have hg := germ_flat U.2 _ hx
  have hs : ((genι Y).stalkMap (ξ (closedPoint _))).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  refine ⟨(hg.comp hs).comp he.1, ?_⟩
  symm
  refine hmm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) ?_
  intro f hf
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem f hf
  rw [Scheme.mem_basicOpen]
  simp only [RingHom.comp_apply] at hu
  exact isUnit_of_map_unit ((genι Y).stalkMap _).hom _ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom _ hu)
  exact hx
end GlobalTheory.LocRegFlat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.zarhinTrick_actions_isomorphic : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : GlobalTheory.ZarhinFam.ord d → (z₁.A ⟶ z₁.A)) (act₂ : GlobalTheory.ZarhinFam.ord d → (z₂.A ⟶ z₂.A)) (inc₁ : c.A ⟶ z₁.A) (pr₁ : z₁.A ⟶ c.A) (inc₂ : c.A ⟶ z₂.A) (pr₂ : z₂.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → IsMonHom inc₁ → IsMonHom pr₁ → inc₁ ≫ pr₁ = 𝟙 c.A → pr₁ ≫ inc₁ = act₁ (GlobalTheory.ZarhinFam.idem d) → IsMonHom inc₂ → IsMonHom pr₂ → inc₂ ≫ pr₂ = 𝟙 c.A → pr₂ ≫ inc₂ = act₂ (GlobalTheory.ZarhinFam.idem d) → (∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc₁ ≫ act₁ (GlobalTheory.ZarhinFam.polUnit d) = 1 ↔ x ≫ inc₂ ≫ act₂ (GlobalTheory.ZarhinFam.polUnit d) = 1) → ∃ e : z₁.A ≅ z₂.A, IsMonHom e.hom ∧ inc₁ ≫ e.hom = inc₂ ∧ ∀ o, act₁ o ≫ e.hom = e.hom ≫ act₂ o := by
  first | (exact @GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (exact GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso) | (intros; apply GlobalTheory.ZarhinUniqIso.zarhin_uniq_iso  <;> assumption)
end
