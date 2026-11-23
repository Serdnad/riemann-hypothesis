module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle636
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle251
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle384
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Formalism.LocalToGlobal.Columns.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle651
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle066

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigMet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem gram_eq_of_isMap {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {F : EigFrame Z φ x} {ψ : R →+* ℂ} {f f' : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f) (hf' : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f') (τ : E →+* ℂ) : G.gram y f' τ = G.gram y f τ := by
  have hc : f.co f' τ = 1 := by
    rw [← f.co_self τ]
    exact EigFrame.co_eq fun i => by rw [hf' τ i, ← hf τ i]; exact f.co_spec f τ i
  rw [G.change y f f' τ, hc, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_comp_evHom {σ : c.F →+* ℂ} {V : (gen Z).affineOpens} {φ : c.F →+* Γ(gen Z, V.1)}
    (hV : LogKS.chart V ≫ genStr Z = spMap φ) {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1) :
    σ = (evHom h).comp φ := by
  have e : spMap σ = spMap ((evHom h).comp φ) := by
    rw [← y.2, ← spMap_evHom h, Category.assoc, hV, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem smoothOn_of_locally {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ))
    (hloc : ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S,
      y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ),
        IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧
        (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧
        ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
          (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (evHom hy) f → G.gram y f τ a b = g y) :
    G.SmoothOn (manifold Z σ) S := by
  classical
  intro V φ F τ a b hV
  have hx : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom h) ≫ LogKS.chart V ≫ genι Z := fun h => by
    rw [← Category.assoc, spMap_evHom h]
  have hex : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom h) f := fun h =>
    F.exists_isMap (evHom h) (eq_comp_evHom hV h) (hx h)
  let g : CxPts (genStr Z) σ → ℂ := fun y =>
    if h : y ∈ ptsIn (genStr Z) σ V.1 then G.gram y (hex h).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
      (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom hy) f → G.gram y f τ a b = g y := fun y hy f hf => by
    simp only [g, dif_pos hy]
    rw [gram_eq_of_isMap G (hex hy).choose_spec hf τ]
  let ι := {y₀ // y₀ ∈ S ∧ y₀ ∈ ptsIn (genStr Z) σ V.1}
  choose T gl hT hmem hre him hagree using fun j : ι => hloc V φ F τ a b hV j.1 j.2.1 j.2.2
  have hc : ∀ y ∈ S ∩ ptsIn (genStr Z) σ V.1, ∃ j, y ∈ T j := fun y hy => ⟨⟨y, hy⟩, hmem _⟩
  have heq : ∀ j, ∀ y ∈ (S ∩ ptsIn (genStr Z) σ V.1) ∩ T j, g y = gl j y := fun j y hy =>
    (hg y hy.1.2 _ (hex hy.1.2).choose_spec).symm.trans (hagree j y hy.2 hy.1.2 _ (hex hy.1.2).choose_spec)
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun j => ((hre j).mono Set.inter_subset_right).congr fun y hy => ?_,
    AnRead.smoothOn_of_cover hT hc fun j => ((him j).mono Set.inter_subset_right).congr fun y hy => ?_,
    fun y _ hy f hf => hg y hy f hf⟩
  · exact congrArg Complex.re (heq j y hy)
  · exact congrArg Complex.im (heq j y hy)

end GlobalTheory.ShFam.EigMet
end
end

section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.FlagMod (ev lieBasis rdet detChg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

section Basis

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}

theorem exists_eigBasis (g : EigFrame Z φ x) : ∃ b : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G),
    ∀ p, b p = g.vec p.1 p.2 := by
  have heig : ∀ (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → R) (b : 𝓞 E),
      actR Z.t.act b (∑ i, a i • g.vec τ i) = φ (embK c τ b) • ∑ i, a i • g.vec τ i := fun τ a b => by

    simp only [map_sum, map_smul, g.act_vec, Finset.smul_sum, smul_comm (a _)]
  have hli : LinearIndependent R (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha p
    have hw := (GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) 0).unique
      (y₁ := fun τ => ∑ i, a ⟨τ, i⟩ • g.vec τ i) (y₂ := fun _ => 0)
      ⟨fun τ b => heig τ _ b, by rw [← ha, Fintype.sum_sigma]⟩ ⟨fun τ b => by simp, by simp⟩
    have h0 := congrFun hw p.1
    exact Fintype.linearIndependent_iff.1 (g.linearIndependent_vec p.1) (fun i => a ⟨p.1, i⟩) h0 p.2
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    intro v _
    obtain ⟨w, ⟨hw, hs⟩, -⟩ := GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) v
    rw [← hs]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := g.existsUnique_sum τ (w τ) (hw τ)
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => by rw [Module.Basis.mk_apply]⟩

def eigBasis (g : EigFrame Z φ x) : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G) :=
  (exists_eigBasis g).choose

theorem eigBasis_apply (g : EigFrame Z φ x) (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eigBasis g p = g.vec p.1 p.2 :=
  (exists_eigBasis g).choose_spec p

def eigBasisFin (g : EigFrame Z φ x) : Module.Basis (Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) R (TanM x Z.t.G) :=
  (eigBasis g).reindex (Fintype.equivFin _)

def frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : R :=
  rdet ((lieBasis M x h).toMatrix (eigBasisFin g))

theorem isUnit_frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : IsUnit (frameDet M h g) :=
  GlobalTheory.FlagMod.isUnit_rdet_toMatrix _ _

theorem ev_detChg_mul_frameDet (M M' : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) (g : EigFrame Z φ x) :
    ev x _ hh (detChg M M').val * frameDet M' h' g = frameDet M h g := by
  rw [GlobalTheory.FlagMod.ev_detChg M M' x h h' hh, frameDet, frameDet, GlobalTheory.FlagMod.rdet_toMatrix_mul]


open Classical in
theorem eigBasis_toMatrix (g g' : EigFrame Z φ x) :
    (eigBasis g).toMatrix (eigBasis g') = Matrix.blockDiagonal' fun τ => g.co g' τ := by
  classical
  ext ⟨σ, b⟩ ⟨τ, i⟩
  have hv : ∀ a, g.vec τ a = eigBasis g ⟨τ, a⟩ := fun a => (eigBasis_apply g ⟨τ, a⟩).symm
  rw [Module.Basis.toMatrix_apply, eigBasis_apply, g.vec_eq g' τ i]

  simp only [hv, map_sum, map_smul, Module.Basis.repr_self]
  by_cases h : σ = τ
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, Finsupp.single_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Finsupp.single_apply, show ∀ a, (⟨τ, a⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≠ ⟨σ, b⟩ from
      fun a e => h (congrArg Sigma.fst e).symm]

open Classical in
theorem frameDet_change (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g g' : EigFrame Z φ x) :
    frameDet M h g' = frameDet M h g * ∏ τ, (g.co g' τ).det := by
  rw [frameDet, frameDet, ← GlobalTheory.FlagMod.rdet_toMatrix_mul _ (eigBasisFin g), GlobalTheory.FlagMod.rdet_self]
  congr 1
  have e : (eigBasisFin g).toMatrix (eigBasisFin g') =
      ((eigBasis g).toMatrix (eigBasis g')).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
    ext i j
    simp [eigBasisFin, Module.Basis.toMatrix_apply]
  rw [e, Matrix.det_submatrix_equiv_self, eigBasis_toMatrix, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']

end Basis

section Flag

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem ev_fromSpecStalk_eq {Y : Scheme.{0}} (x : Y) {V : Y.Opens} (hx : x ∈ V) (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V)
    (u : Γ(Y, V)) : ev (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem top_le_stalk_preimage {X Y : Scheme.{0}} (y : X) (f : X ⟶ Y) {V : Y.Opens} (hy : f y ∈ V) :
    ⊤ ≤ (X.fromSpecStalk y ≫ f) ⁻¹ᵁ V := by
  intro z _
  have hz : X.fromSpecStalk y z ⤳ y := by
    have : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (hz.map f.continuous).mem_open V.isOpen hy

theorem fnOf_app_eq_ev {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) {V : Y.Opens} (hg : genericPoint X ∈ f ⁻¹ᵁ V)
    (hh : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ f) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    fnOf (f ⁻¹ᵁ V) hg ((f.app V).hom a) = ev (X.fromSpecStalk (genericPoint X) ≫ f) V hh a := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ V) := top_le_stalk_preimage (genericPoint X) (𝟙 X) hg
  refine (ev_fromSpecStalk_eq (genericPoint X) hg h1 _).symm.trans (Eq.trans ?_
    (GlobalTheory.FlagMod.ev_appLE (X.fromSpecStalk (genericPoint X)) f le_rfl h1 hh a))
  rw [Scheme.Hom.app_eq_appLE]

variable {C}

variable (C)


end Flag

section Presents

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

end Presents

section Presents2

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem isEqn_finset_sum {X : Scheme.{0}} [IsIntegral X] {T : Type} (s : Finset T) (D : T → CartierDiv X) (y : X)
    (t : T → X.functionFieldˣ) (ht : ∀ i, (D i).IsEqn y (t i)) : (∑ i ∈ s, D i).IsEqn y (∏ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (ht a).add ih

end Presents2

end GlobalTheory.ShFam
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw



theorem seed_at_enl : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∃ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ hgrp _ core' alg' _ _ hKs _ _ _ _ _

  set Wt' : Set B'.places.Pl := {v | B'.places.resChar v ∈ T'.pl} with hWt
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  have hok := w'.ok
  have hC := w'.C_eq
  have hrange := w'.xi_range
  have hsel : SelHalf w'.I := by
    intro a b P hP P' hP' hq
    obtain ⟨q, hq, hqP, hqP'⟩ := hq
    obtain ⟨v, -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP
    obtain ⟨v', -, rfl⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hP'
    have hab : ∀ v, (w'.I.sel v).under (𝓞 B'.host.F) = v := fun v => by
      have h := pin.above v
      unfold Formalism.L2.Host.aboveF at h
      rw [Set.Finite.mem_toFinset] at h
      exact h
    have hmem : ∀ v, ((q : 𝓞 B'.host.E) ∈ (w'.I.sel v).asIdeal) → (q : 𝓞 B'.host.F) ∈ v.asIdeal := fun v h => by
      rw [← hab v]
      show (q : 𝓞 B'.host.F) ∈ (w'.I.sel v).asIdeal.comap (algebraMap _ _)
      rw [Ideal.mem_comap, map_natCast]
      exact h
    have := pin.half v v' q hq (hmem v hqP) (hmem v' hqP')
    exact congrArg HeightOneSpectrum.asIdeal this
  have hfin : Wt'.Finite := GlobalTheory.Mem.Top.TwFin.finite_pl B' T'.pl
  have hconj : ∀ v ∈ Wt', B'.places.conj v ∈ Wt' :=
    fun v hv => by simpa only [hWt, Set.mem_setOf_eq, GlobalTheory.Mem.Top.TwFin.resChar_conj] using hv
  have hch : Fld.charField f' ≤ B'.KsC := (GlobalTheory.Mem.Base.KsExact.lower w'.exact).2.2.1
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' hok hC hrange
  have hrange' : Set.range w'.I.xi = T'.set w'.I.C := by rw [hC]; exact hrange
  have hCK : ∀ x ∈ (w'.st Z').B.Ks, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = x := hKs
  have hCE : ∀ x : (w'.st Z').toD7.host.E, ∃ y : core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y = (w'.st Z').toD7.embE x :=
    fun x => hKs _ (B'.E_le_Ks x)
  have hmu : ∀ (L : Formalism.IndefR.Links.LevCh (w'.st Z').toD7 (TupU w'.I (usedOf w'.I T' Wt'))),
      L.Is (mu0F (X := (w'.st Z').B.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) → L.C = Top.Fr.at (w'.st Z') w'.I.C →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (x : (AE (w'.st Z').toD7)ˣ), infPart (w'.st Z').toD7 (x : AE (w'.st Z').toD7) = 1 →
        ∃ y : core'.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) := by
    intro L hL hLC i x hx
    have hLC' : L.C = Fr.at (w'.st Z') f' := hLC.trans (by rw [hC])
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ Formalism.L2.Pj.FO (w'.st Z').toD7 := by
      refine GlobalTheory.CoreExact.char_mem_of_values (w'.st Z').toD7 _ _ (hL.mu0 i) (Formalism.L2.Pj.FO (w'.st Z').toD7) ?_ ?_ x hx
      · rw [hLC', ← GlobalTheory.CoreExact.KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f'.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => ((w'.st Z').toD7.hc ((w'.st Z').toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (Formalism.L2.Pj.conj_mem_FO _ _ _) (Formalism.L2.Pj.conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨x₁, hx₁, hx₁'⟩ := (mem_FO_assembled_iff (w'.st Z') _).1 hmem
    obtain ⟨y, hy⟩ := hCK x₁ hx₁
    exact ⟨y, by rw [hy]; exact hx₁'.symm⟩
  exact GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices (w'.st Z') w'.px w'.I hX' T' Wt' core'.Q.c.F h6 hfin hconj hok hrange' hsel hgrp hVals hHH hStd hStdX hPos hCK hCE hmu

end GlobalTheory.Mem.R3.Rw

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_exponentialChart_rescale_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | exact GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isExpChart_rescale <;> assumption)
end
