module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle644
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631

@[expose] public section

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_levelGroup_transport_uniformisation_components : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  first | exact @GlobalTheory.ShareOn.exists_transport | exact GlobalTheory.ShareOn.exists_transport | (intros; apply GlobalTheory.ShareOn.exists_transport <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames frX frVec)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem tv_vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X}
    (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx
  rfl

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (Q Q' : FrPt Xo c S)
    (e : Q'.x = Q.x) : ∃ u : Sˣ, ∀ e : Q'.x = Q.x, ∀ i, (e ▸ Q'.s).f i = scal Q.x (u : S) i * Q.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨u0, fun _ => hu0⟩

theorem rel_unique : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  intro E _ _ _ H Dw l Xo c Y X C _ hC K _ z z' p hp hr hr'
  obtain ⟨φ, k, hk, g, hφ, hg, hc⟩ := hr
  obtain ⟨φ', k', hk', g', hφ', hg', hc'⟩ := hr'
  have e1 : p ≫ C.π ≫ genι Y = z ≫ X.π := carries_over C hc
  have e2 : p ≫ C.π ≫ genι Y = z' ≫ X.π := carries_over C hc'
  have hπ : z' ≫ X.π = z ≫ X.π := e2.symm.trans e1
  have ephi : φ' = φ := by
    have h0 : spMap φ' = spMap φ := by rw [← hφ', ← hφ, ← Category.assoc, hπ, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst ephi
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ' (z ≫ X.π), ∀ τ i, g0.v τ i = g'.v τ i := by
    rw [← hπ]; exact ⟨g', fun _ _ => rfl⟩
  have hc0 : C.Carries p g0 := (carries_congr C hπ.symm g0 g' hg0 p).2 hc'
  obtain ⟨t, ht⟩ := hC K _ _ (z ≫ X.π) p g g0 hc hc0
  letI : Algebra c.F K := φ'.toAlgebra
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hxg : (p ≫ C.π) ≫ genι Y = z ≫ X.π := by rw [Category.assoc]; exact e1
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have := hp a
    rw [Scheme.Hom.comp_apply]
    exact this
  have := Y.jQ_open
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy0 : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hyj : z ≫ X.π = y ≫ Y.j := by
    rw [Model.j, ← Category.assoc, hy0, ← hxg]
  have hstr : genStr Y = genι Y ≫ Y.s := by
    calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← Y.jQ_over, ← Category.assoc, hy0]
    show (p ≫ C.π) ≫ genStr Y = _
    rw [hstr, ← Category.assoc, hxg, Category.assoc]
    exact hφ
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hyj k hk
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr hy (hπ.trans hyj) k' hk'
  have hx : frX Q ≫ Y.j = z ≫ X.π := hQ.over
  have hx' : frX Q' ≫ Y.j = z ≫ X.π := hQ'.over.trans hπ
  have eQ : Q'.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := Y) (GlobalTheory.FlagMod.frX_snd Q') (GlobalTheory.FlagMod.frX_snd Q) (hx'.trans hx.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q Q' eQ
  choose cf hcf1 hcf2 hcf3 using ht.2.2
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  let T : Ix Dw → Kˣ := fun ix => match ix with | none => u0 | some q => t q.1 q.2
  have hB : FrBor T Q Q' := by
    refine GlobalTheory.FlagMod.frBor_of_frVec (X.F.inM hk rfl) hx hx' T (fun σ j i => cf σ i j)
      (fun σ r s hrs => hcf2 σ s r hrs) (fun σ i => hcf1 σ i) (fun σ i => ?_) hu0
    rw [hQ'.frVec_eq hπ hx', hQ.frVec_eq rfl hx]
    refine (GlobalTheory.LieMet.isComb_iff _ _ _).1 ?_
    have h3 := hcf3 σ i
    simp only [h1, Category.id_comp] at h3
    rw [hg0 σ i, hg' σ i, ← tv_vecAt_congr X.F k' z' hk' hπ σ i] at h3
    have e : (fun j => g.v σ j) = fun j => (tv (X.F.vecAt k z hk rfl σ j)).left := funext (hg σ)
    rw [e] at h3
    exact h3
  exact (X.rep K Q').unique (hQ.lies.frBor hB) hQ'.lies

end GlobalTheory.VarFlag
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open GlobalTheory.Toroidal (gen genι genStr)

theorem exists_rel_of_mem_Vo : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (B : GlobalTheory.ProjVar.Var c.F) (j : B.X ⟶ GlobalTheory.Toroidal.gen Y) [IsOpenImmersion j] (f : C.Y.X ⟶ B.X), C.π = f ≫ j → (∀ w : GlobalTheory.Toroidal.gen Y, GlobalTheory.Toroidal.genι Y w ∈ GlobalTheory.CompHS.barComp Y Z ↔ w ∈ Set.range j) → ∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → ∃ z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X Z, GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X Z) p := by
  intro E _ _ _ H Dw l Xo c Y X Z hFE C _ B j _ f hπ hbar K _ p hp

  obtain ⟨yF, hyF, hcar⟩ := GlobalTheory.Mean4O.CompModel.exists_flagPt C p

  haveI := Y.jQ_open
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hp s
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hys : y ≫ pullback.snd _ _ = spMap yF.fK := by
    rw [← Y.jQ_over, ← Category.assoc, hy, hyF]
    exact yF.y_over

  obtain ⟨P, hPy, hPw⟩ := GlobalTheory.ShFam.exists_frPt_ptF_over_of_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) Y K yF.fK y
    (yF.y ≫ genι Y) yF.frame hys (by rw [← Category.assoc, hy, hyF])
  letI : Algebra c.F K := yF.fK.toAlgebra
  have hPX : GlobalTheory.FlagMod.frX P = y := hPy
  have hl := X.lies_ptY P
  have hxg : X.ptY P ≫ X.π = yF.y ≫ genι Y := by
    rw [hl.1, hPX, Model.j, ← Category.assoc, hy, hyF]

  have hr₀ : Set.range (X.ptY P) ⊆ Set.range (GlobalTheory.CompHS.inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    show X.π (X.ptY P s) ∈ GlobalTheory.CompHS.barComp Y Z
    have e : X.π (X.ptY P s) = genι Y (j (f (p s))) := by
      rw [← Scheme.Hom.comp_apply, hxg, ← hyF, hπ]
      rfl
    rw [e]
    exact (hbar _).2 ⟨f (p s), rfl⟩
  let z := IsOpenImmersion.lift (GlobalTheory.CompHS.inc₀ X Z) (X.ptY P) hr₀
  have hz : z ≫ GlobalTheory.CompHS.inc₀ X Z = X.ptY P := IsOpenImmersion.lift_fac _ _ _
  refine ⟨z, ?_⟩
  rw [hz]

  obtain ⟨k, hk⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover (X.ptY P)
  have hφ : X.ptY P ≫ X.π ≫ Y.s = spMap yF.fK := GlobalTheory.CompHS.ptY_str X P
  obtain ⟨g₂, hg₂⟩ := hFE K yF.fK (X.ptY P) k hk hφ
  refine ⟨yF.fK, k, hk, g₂, hφ, hg₂, ?_⟩

  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd P) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have ht' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K).2.2.1 _ _ _ ht
  have hPx : GlobalTheory.FlagMod.frX P ≫ Y.j = X.ptY P ≫ X.π := hl.1.symm
  choose b hb hdiag hsum using fun τ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (X.F.M k).toMChart) (X.F.inM hk rfl) hPx hQ.over ht' τ

  have hgv : ∀ τ i, yF.frame.v τ i = (tv (GlobalTheory.FlagMod.frVec Y P hPx τ i)).left := by
    intro τ i
    obtain ⟨w, hw1, hw2, hw3⟩ := hPw τ i
    rw [← hPX] at hw1
    have hL : w = GlobalTheory.FlagMod.liftTan Y (GlobalTheory.FlagMod.frX P) ((GlobalTheory.FlagMod.frX_fst P).symm ▸ P.tan τ i) :=
      Y.m0.cart.1.hom_ext (hw2.trans (GlobalTheory.FlagMod.liftTan_univ _ _).symm)
        (hw1.trans (GlobalTheory.FlagMod.liftTan_over _ _).symm)
    show yF.frame.v τ i = _
    rw [← hw3, hL]
    rfl
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have h2 : spMap (RingHom.id K) = 𝟙 _ := Spec.map_id _
  have hd : yF.frame.Tri (RingHom.id K) g₂ (fun τ i => (t⁻¹) (some ⟨τ, i⟩)) := by
    refine ⟨by rw [h2, Category.id_comp, hxg], rfl, fun τ i => ⟨fun m => b τ m i, hdiag τ i,
      fun m hm => hb τ hm, ?_⟩⟩
    simp only [h1, Category.id_comp]
    have e : (fun m => yF.frame.v τ m) = fun m => (tv (GlobalTheory.FlagMod.frVec Y P hPx τ m)).left := funext (hgv τ)
    rw [e, hg₂ τ i, GlobalTheory.LieMet.isComb_iff, ← hQ.frVec_eq rfl hQ.over τ]
    exact hsum τ i
  exact carries_of_tri C hd hcar

end GlobalTheory.VarFlag
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
open GlobalTheory.ShFam.BdArc GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.CompHS

theorem evalPt_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (ψ : Γ(X, U) →+* R) (h : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) ⁻¹ᵁ U) :
    GlobalTheory.TangentOrigin.evalPt (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) U h = ψ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem exists_extension_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  intro E _ _ _ H Dw l Xo c Y X Z la σ m hm W hW i p hi hdom hsm hp hbd
  have hPW : (Y₀ X Z).basicOpen p ≤ W := (Y₀ X Z).basicOpen_le p
  have hPU : (Y₀ X Z).basicOpen p ≤ U₀ X Z := fun y hy => by
    by_contra h
    exact (hbd y (hPW hy)).1 h hy
  have hPL : (Y₀ X Z).basicOpen p ≤ U₀ X Z ⊓ (L₀ X Z la).U i := le_inf hPU (hPW.trans hi)
  have := hW.isLocalization_basicOpen p
  obtain ⟨⟨a, _, M, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) (resG _ hPL (m.loc i))
  have e' : resG _ hPL (m.loc i) * resG _ hPW (p ^ M) = resG _ hPW a := e
  have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)) =
      (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z := Spec.map_preimage _
  letI : Algebra c.F Γ(Y₀ X Z, W) :=
    (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom.toAlgebra
  obtain ⟨b, hab, hb⟩ := exists_eq_mul_pow_of_tendsto_zero c.F Γ(Y₀ X Z, W) hsm σ p a M hp
    fun ψ r hψ hσ h0 h1 => by
      have hlim := hm W hW i hi ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hbd _ (spMap_fromSpec_mem hW _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hW _ p s).1 h h0)
        (fun u hu hu0 s _ => hPU ((spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hu hu0)))
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hψ.1
      filter_upwards [hlim ε hε, mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hub hu0
      have hWx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ W :=
        fun s _ => spMap_fromSpec_mem hW _ s
      have hPx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (Y₀ X Z).basicOpen p :=
        fun s _ => (spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hub hu0)
      have hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z :=
        fun s hs => hPU (hPx hs)
      have hiu : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i :=
        fun s hs => hi (hWx hs)
      have hev := evalPt_spMap_fromSpec hW (ψ u) hWx
      have hpu : ψ u (p ^ M) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (h1 u hub hu0)
      have hmul : H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hiu m * ψ u (p ^ M) =
          ψ u a := by
        have e₁ := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hPx) e'
        rw [map_mul, GlobalTheory.TangentOrigin.evalPt_res _ hPL (GlobalTheory.TopForm.le_preimage_inf hO hiu) hPx,
          GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, hev] at e₁
        exact e₁
      rw [dist_zero_right, ← hmul, mul_div_cancel_right₀ _ hpu]
      exact hu hO hiu
  refine ⟨b, fun y' h h' => ?_, fun y' h hy => ?_⟩
  · have hyP : y' ∈ (Y₀ X Z).basicOpen p := by
      by_contra hn
      exact (hbd y' h).2 hn h'
    have hunit : IsUnit (ger y' h p) := ((Y₀ X Z).mem_basicOpen p y' h).1 hyP
    have hunit' : IsUnit (ger y' h (p ^ M)) := by
      rw [map_pow]
      exact hunit.pow M
    have e₁ := congrArg (ger y' hyP) e'
    rw [map_mul, ger_resG, ger_resG, ger_resG, hab, map_mul] at e₁
    exact (hunit'.mul_right_cancel e₁).symm
  · have hyP : y' ∉ (Y₀ X Z).basicOpen p := (hbd y' h).1 hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨n, hn⟩ := hb
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    refine hyP (((Y₀ X Z).mem_basicOpen p y' h).2 ?_)
    have h₂ := hu.pow n
    rw [← map_pow, ← hd, map_mul] at h₂
    exact isUnit_of_mul_isUnit_right h₂

end GlobalTheory.CompHS
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.exists_lieDeterminantLine_ratio_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q), FrameCover t π s V (HermitianCompactForm.chi c τ) p q → IsSection t π s V (HermitianCompactForm.chi c τ) σ → NowhereZero t π s V (HermitianCompactForm.chi c τ) σ → IsSection t π s V (HermitianCompactForm.chi c τ) σ' → ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  first | exact @GlobalTheory.detLine_exists_ratio | exact GlobalTheory.detLine_exists_ratio | (intros; apply GlobalTheory.detLine_exists_ratio <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  first | exact @GlobalTheory.DetLine.exists_unif_of_frame | exact GlobalTheory.DetLine.exists_unif_of_frame | (intros; apply GlobalTheory.DetLine.exists_unif_of_frame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) (e : c.F →+* ℂ), SecU Xo c U τ σ → IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.isFlatAt_of_conj | exact GlobalTheory.isFlatAt_of_conj | (intros; apply GlobalTheory.isFlatAt_of_conj <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_bar (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R]
    {x : Sp R ⟶ Xo.XF c} {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} (h : ∃ j, FrU Xo c U τ j x v w) :
    ∃ vb wb, FrY Y (compactOf Y U) τ h.choose (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb :=
  (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R h.choose x).1 v w h.choose_spec

def restrictRule (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y) : RuleU Xo c :=
  fun R _ x v w =>
    haveI := Classical.propDecidable (∃ j, FrU Xo c U τ j x v w)
    if h : ∃ j, FrU Xo c U τ j x v w then
      σb R (x ≫ Y.jQ) (exists_bar Y U τ h).choose (exists_bar Y U τ h).choose_spec.choose
    else 0

theorem restrictRule_eq (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {σb : RuleY Y}
    (hσb : SecY Y (compactOf Y U) τ σb) {R : Type} [CommRing R] {j : c.F →+* R} {x : Sp R ⟶ Xo.XF c}
    {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin D.p → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} {wb : Fin D.q → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)}
    (h : FrU Xo c U τ j x v w) (hb : FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb) (hv : SameVecs Y x v vb)
    (hw : SameVecs Y x w wb) : restrictRule Y U τ σb R x v w = σb R (x ≫ Y.jQ) vb wb := by
  have hex : ∃ j, FrU Xo c U τ j x v w := ⟨j, h⟩
  obtain ⟨hb0, hv0, hw0⟩ := (exists_bar Y U τ hex).choose_spec.choose_spec
  have e : restrictRule Y U τ σb R x v w =
      σb R (x ≫ Y.jQ) (exists_bar Y U τ hex).choose (exists_bar Y U τ hex).choose_spec.choose := by
    unfold restrictRule
    rw [dite_eq_left hex]
  rw [e]
  have hx : x ≫ Y.jQ = spMap (RingHom.id R) ≫ (x ≫ Y.jQ) := by
    rw [DetExtendZero.spMap_id, Category.id_comp]
  have hx' : x = spMap (RingHom.id R) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
  have cv : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.p) (Fin D.p) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (vb k).left) ((exists_bar Y U τ hex).choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.p v vb v _ hx' hv hv0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.1.1 k).1) i
  have cw : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.q) (Fin D.q) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (wb k).left)
      ((exists_bar Y U τ hex).choose_spec.choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.q w wb w _ hx' hw hw0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have key := sec_chg hσb hb hb0 (g := RingHom.id R) (M := 1) (N := 1) ⟨hx, cv, cw⟩
  simpa using key.symm

theorem exists_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ σb hσb
  refine ⟨restrictRule Y U τ σb, isSection_of_chg ?_, ?_, ?_⟩
  · intro R R' _ _ g j j' x v w x' v' w' M N h h' hc
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    obtain ⟨vb', wb', hb', hv', hw'⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R' j' x').1 v' w' h'
    rw [restrictRule_eq Y U τ hσb h hb hv hw, restrictRule_eq Y U τ hσb h' hb' hv' hw']
    refine sec_chg hσb hb hb' ⟨by rw [hc.1, Category.assoc], fun i => ?_, fun i => ?_⟩
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.p v vb v' vb' hc.1 hv hv'
        _ i).mp (hc.2.1 i)
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.q w wb w' wb' hc.1 hw hw'
        _ i).mp (hc.2.2 i)
  · intro R _ j x v w vb wb h hb hv hw
    exact (restrictRule_eq Y U τ hσb h hb hv hw).symm
  · intro hnz R _ j x v w h
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    rw [restrictRule_eq Y U τ hσb h hb hv hw]
    exact hnz R j _ vb wb hb

end GlobalTheory.DetLine.Restrict
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

theorem _root_.GlobalTheory.T.moduliScheme_affineFrameCover_two_eigenParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) D.p D.q := by
  first | exact @GlobalTheory.DetLine.frameCover_univ | exact GlobalTheory.DetLine.frameCover_univ | (intros; apply GlobalTheory.DetLine.frameCover_univ <;> assumption)
end
