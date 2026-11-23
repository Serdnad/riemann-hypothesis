module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.WeilBound.CoreStatements.ProjectiveValuations.Bundle001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle260
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle289
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle293
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CompanionTheory.FlagMod

theorem cells_smooth_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, Z ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ Z)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∃ d : ℕ, SmoothOfRelativeDimension d (π ≫ Y.s) ∧ IsProjOver (π ≫ Y.s) :=
  @DifferentiableLines.flag_embedding_atlas_projective

end GlobalTheory.CompanionTheory.FlagMod
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.exponential_surjective_semiabelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective <;> assumption)
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.RdEx

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (Formalism.L2.Pj.dualMap g) ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap (Formalism.L2.Pj.dualMap (g.comp f)) := by
  rw [spMap_comp']
  congr 1
  refine RingHom.ext fun t => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]



theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → ∃ Rd : Reading Fr h Z, GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Fr h Z hcomp hgt hWD
  letI := Small.cstAlg Or
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv E H Dw l Xo c Y SS RM Sys Fx Or Z hcomp
  obtain ⟨hyx, y₀, hy₀, hcomb⟩ := isGenFr_genFr h Z
  let χ : kap Z →ₐ[c.F] RM.Ω := { Or.𝔐.fn.comp ψ.toRingHom with commutes' := hψ2 }
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.FrameNorm.exists_frMap_along χ y₀
  obtain ⟨hpt₂, hlie⟩ := GlobalTheory.T.root_origin_component_iso_relay E H Dw l Xo c Y SS RM Sys Fx Or Z ψ hψ1 y₀ hy₀ χ y₂ rfl hy₂
  choose e he hi hev using hlie
  letI fa := Or.𝔐.fn.toAlgebra
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hb, hT0, hTd⟩ := GlobalTheory.T.generic_flag_triangular_relay Or.𝔐.Ω₀ RM.Ω Or.Fl.Li₀ Or.𝔐.Li Or.Fl.j
    (CMType H ⊕ CMType H) (labelRk Dw) Or.Fl.V₀ Or.Fl.b Or.Fl.deg Or.Fl.generic e he hi
  obtain ⟨T, hTi, hTr, hTv⟩ := GlobalTheory.T.flag_variables_alg_indep E H Dw Or.𝔐.Ω₀ RM.Ω v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := GlobalTheory.T.polynomial_field_extension_degree (kap Z) Or.𝔐.Ω₀ RM.Ω (FlagVar Dw) ψ T hTi
  have hφk : ∀ a : kap Z, φ (algebraMap (kap Z) (Om Z) a) = Or.𝔐.fn (ψ a) := fun a => hφC a
  have hφcst : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [← hψ2 a, ← hφk]
    rfl
  let φa : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφcst }
  obtain ⟨y', hy'⟩ := GlobalTheory.FrameNorm.exists_frMap_along φa (genFr h Z)
  have hφχ : φ.comp (algebraMap (kap Z) (Om Z)) = χ.toRingHom := RingHom.ext hφk
  have hxx : y'.x = y₂.x := by
    rw [hy'.1, hy₂.1, hyx, hy₀]
    show spMap φ ≫ spMap _ ≫ _ = spMap χ.toRingHom ≫ _
    rw [← Category.assoc, spMap_comp', hφχ]
  have hptF : Small.ptF y' = Small.ptF y₂ := pullback.hom_ext (by rw [Small.ptF_fst, Small.ptF_fst, hxx])
    (by rw [Small.ptF_snd, Small.ptF_snd])
  have hpt' : Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f := by
    rw [← hpt₂, Small.ptY, Small.ptY, hptF]
  have hcoef : ∀ (s : CMType H ⊕ CMType H) (k m : Fin (labelRk Dw s)),
      φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) (Small.labelFin Dw s m)) = v s m k := by
    intro s k m
    unfold genCoef
    split_ifs with h1 h2
    · have := hφX ⟨Small.labelC s, ⟨(Small.labelFin Dw s k, Small.labelFin Dw s m), h1⟩⟩
      refine this.trans ((hTv s _ _ h1).trans ?_)
      rfl
    · have : k = m := Fin.ext (show (k : ℕ) = m from congrArg (fun x : Fin (Dw.mult (Small.labelC s)) => (x : ℕ)) h2)
      subst this
      rw [map_one, hv1]
    · have : m < k := by
        have h3 : ¬ (k : ℕ) < m := h1
        have h4 : (k : ℕ) ≠ m := fun e' => h2 (Fin.ext e')
        exact Fin.lt_def.2 (by omega)
      rw [map_zero, hv0 s m k this]
  have hc : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk Dw s)),
      IsCombAt y₂.x (y₂.u (Small.labelC s))
        (fun j => φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) j))
        (y'.u (Small.labelC s) (Small.labelFin Dw s k)) := by
    intro s k
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isCombAt_bc (ψ := φ) (x0 := (genFr h Z).x) (x0' := y'.x) hy'.1
      (hcomb (Small.labelC s) (Small.labelFin Dw s k))
    have h2 : ∀ j, spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j = y₂.u (Small.labelC s) j := fun j => by
      rw [hy₂.2.1, ← Category.assoc, spMap_dual_comp', hφχ]
    have h3 : y'.u (Small.labelC s) (Small.labelFin Dw s k) = spMap (Formalism.L2.Pj.dualMap φ) ≫ (genFr h Z).u (Small.labelC s) (Small.labelFin Dw s k) := hy'.2.1 _ _
    rw [h3, ← hxx]
    simpa only [h2] using h1
  let Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li := fun s m => ∑ k, v s k m • Or.Fl.j (e s k)
  have hW : ∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
    intro s k
    have := GlobalTheory.T.root_origin_constant_algebra_points E H Dw l Xo c Y SS RM Sys Fx Or y₂ y' hpt₂ hxx s (fun m => Or.Fl.j (e s m)) (hev s) _ k (hc s k)
    simpa only [hcoef] using this
  obtain ⟨t, hbor⟩ := GlobalTheory.T.root_origin_generic_frame_constants E H Dw l Xo c Y SS RM Sys Fx Or Fr y' hpt' Wv Tm hW hb hT0 hTd
  refine ⟨⟨φ, hφcst, t, fun a f hf => ?_, ?_⟩, y', hy', hbor⟩
  · have h1 := GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field E H Dw l Xo c a f RM.Ω t y' Fr.y₀ hf hbor
    obtain ⟨p, ψ₁, z, hz⟩ := hgt
    have key : ∀ {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ' : p.R →ₐ[c.F] S), FrMap ψ' z w →
        evR Xo c f w = ψ' (f p z) := by
      intro S _ _ w ψ' hw
      have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, ψ', z, hw⟩
      show evalAt _ _ f w = _
      unfold evalAt
      rw [dite_eq_left hft]
      exact hWD f hf.1 S _ p _ ψ' _ z w hft.choose_spec.choose_spec.choose_spec hw
    have h2 : evC h Z f = ψ₁ (f p z) := key _ _ hz
    have h3 : evR Xo c f y' = φ (evC h Z f) := by
      rw [key y' (φa.comp ψ₁) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ₁ φa hz hy'), h2]
      rfl
    show evR Xo c f Fr.y₀ = _
    rw [h1, h3]
  · have h1 := hφd
    rw [hTr, hvd] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.Plug.RdEx

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem exists_geoRead : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ (Fr : Small.GenFrame (o.Or B (κ Z))) (Rd : Reading Fr h Z), GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c r U h e hl Y T o κ hκ B Z
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z))
    (o.Or B (κ Z))
  obtain ⟨Rd, hR⟩ := RdEx.core E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z)) (o.Or B (κ Z)) Fr h Z
    (hκ Z) (hl.genT Z) hl.evalWD
  exact ⟨Fr, Rd, hR⟩

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]

def epsIso (R : Type) [CommRing R] : epsR R ≅ epsAt (𝟙 (Sp R)) :=
  Over.isoMk (Iso.refl _) (by simp [spMap])

def tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : epsR R ⟶ G := (epsIso R).hom ≫ M.pt x

theorem tanVec_left (M : LieModel G (𝟙 (Sp R)) E) (x : E) : (tanVec M x).left = (M.pt x).left := by
  simp [tanVec, epsIso]

theorem one_left : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  have h : (toUnit (Over.mk (𝟙 (Sp R)))).left = 𝟙 _ := by
    have := Over.w (toUnit (Over.mk (𝟙 (Sp R))))
    simpa using this
  rw [h]
  exact Category.id_comp _

theorem isTangent_tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : IsTangent (tanVec M x) := by
  have h := M.tan x
  unfold IsTangent
  rw [tanVec_left]
  exact h.trans one_left

theorem exists_tanVec (M : LieModel G (𝟙 (Sp R)) E) (w : epsR R ⟶ G) (hw : IsTangent w) : ∃ x, tanVec M x = w := by
  obtain ⟨x, hx⟩ := M.onto ((epsIso R).inv ≫ w) (by
    unfold IsTanAt
    have e : ((epsIso R).inv ≫ w).left = w.left := by simp [epsIso]
    rw [e]
    exact Eq.trans hw one_left.symm)
  exact ⟨x, by rw [tanVec, hx]; simp⟩

theorem tanVec_injective (M : LieModel G (𝟙 (Sp R)) E) : Function.Injective (tanVec M) := fun a b h =>
  M.inj (Over.OverMorphism.ext (by rw [← tanVec_left, ← tanVec_left, h]))

theorem prod_ofFn_tanVec (M : LieModel G (𝟙 (Sp R)) E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => tanVec M (f j)).prod = tanVec M (∑ j, f j)
  | 0, f => by simp [tanVec, M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_tanVec M, Fin.sum_univ_succ]
    simp only [tanVec, M.add, MonObj.comp_mul]

theorem isLieComb_tanVec_iff (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (c : Fin n → R) (x : E) :
    IsLieComb c (fun i => tanVec M (b i)) (tanVec M x) ↔ x = ∑ i, c i • b i := by
  have hs : ∀ i, (tanVec M (c i • b i)).left = spMap (epsScaleR (c i)) ≫ (tanVec M (b i)).left := fun i => by
    rw [tanVec_left, tanVec_left, M.smul]
    rfl
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tanVec M (c i • b i) := funext fun i =>
      Over.OverMorphism.ext ((hu i).trans (hs i).symm)
    rw [hu', prod_ofFn_tanVec M] at hw
    exact tanVec_injective M hw
  · rintro rfl
    exact ⟨fun i => tanVec M (c i • b i), hs, (prod_ofFn_tanVec M _).symm⟩

theorem isLieBasis_tanVec (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (hli : LinearIndependent R b)
    (hsp : Submodule.span R (Set.range b) = ⊤) : IsLieBasis (fun i => tanVec M (b i)) := by
  refine ⟨fun i => isTangent_tanVec M _, fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := exists_tanVec M w hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp ▸ Submodule.mem_top : x ∈ Submodule.span R (Set.range b))
  refine ⟨c, (isLieComb_tanVec_iff M b c x).2 hc.symm, fun c' h => ?_⟩
  have h' := (isLieComb_tanVec_iff M b c' x).1 h
  have h0 : ∑ i, (c' i - c i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h', hc, sub_self]
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

end Lie

section Sec

variable {X : Scheme.{0}}

theorem mem_basicOpen_map {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

theorem sameSec_ofPow {L : LB X} (s : Out.H0 L 1) : KeyDeg.SameSec s (GlobalTheory.GeneratorFrame.ofPow s) := fun _ => rfl

theorem nonzeroLocus_ofPow {L : LB X} (s : Out.H0 L 1) {y : X} (hy : y ∈ Out.nonzeroLocus s) :
    y ∈ Out.nonzeroLocus (GlobalTheory.GeneratorFrame.ofPow s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, rfl⟩ : ∃ i, k = fun _ => i := ⟨k 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have hU : y ∈ L.U i := GlobalTheory.GeneratorFrame.wchart_le' L (fun _ => i) (X.basicOpen_le _ hk)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (mem_basicOpen_map _ _ y).2 ⟨hU, hk⟩⟩

end Sec

section Main

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Chart.dualMapR f = dualMap f := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR, dualMap]

theorem mem_basicOpen_appLE {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (f : Γ(X, U))
    {z : Y} (hz : z ∈ V) (hy : φ z ∈ X.basicOpen f) : z ∈ Y.basicOpen ((φ.appLE U V h).hom f) := by
  have e : (φ.appLE U V h).hom f = (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom f) := rfl
  rw [e]
  refine (mem_basicOpen_map h _ z).2 ⟨hz, ?_⟩
  rw [← Scheme.preimage_basicOpen]
  exact hy

theorem exists_keyIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  intro E _ _ _ H L _ _ D hg s e hs hli hsp
  have sm := D.tK.semi.smooth
  have gc := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hnv : KeyDeg.NonVan D.t.G.hom (GlobalTheory.GeneratorFrame.ofPow s) := fun b => by
    obtain ⟨y, hy, hy'⟩ := hs b
    exact ⟨y, hy, nonzeroLocus_ofPow s hy'⟩
  have hv := isLieBasis_tanVec D.MB e hli hsp
  obtain ⟨v', hv', hφ⟩ := GlobalTheory.exists_isLieBasis_baseChange (𝓞 L) L (algebraMap (𝓞 L) L) D.t.G D.tK.G D.m.φ D.m.cart
    D.t.semi.smooth D.g _ hv
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis D.tK.G hd
  have hdg : d = D.g := GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis D.m.cart hu hv'
  rw [hdg] at hd
  obtain ⟨hp, ha, hk⟩ := D.princ
  obtain ⟨w, hw, hr, -⟩ := D.m.lin
  have hw' := (isGen_iff w).1 hw
  obtain ⟨xth, hx⟩ := sec_pull_down hw' D.t.PP.isLB D.tK.PP.isLB (GlobalTheory.GeneratorFrame.ofPow s)
  have hcompat : ∀ (j : (D.t.PP.L.pull D.m.φ).ι) (i : D.tK.PP.L.ι)
      (h : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U (j PUnit.unit)),
      (D.m.φ.appLE _ _ h).hom ((GlobalTheory.GeneratorFrame.ofPow s).f (j PUnit.unit)) =
        (show Γ(D.tK.G.left, (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (xth.f i) := fun j i h => fn_ext fun y hy =>
    (gs_appLE D.m.φ _ _ h (𝟙 _) y hy _).trans ((hx _ (𝟙 _) y _ i (h hy) hy.2).trans
      (Eq.symm ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res (𝟙 _) y _ hy _)))))
  have hne : ∀ s₀ : Sp L, ∃ z : D.tK.G.left, D.tK.G.hom z = s₀ ∧ z ∈ Out.nonzeroLocus xth := fun s₀ => by
    obtain ⟨y, hy, hyn⟩ := hnv (spMap (algebraMap (𝓞 L) L) s₀)
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback D.m.cart.1 y s₀ hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hyn
    obtain ⟨i, hi⟩ := exists_chart D.tK.PP.isLB z
    have hU : D.m.φ z ∈ D.t.PP.L.U l := Scheme.basicOpen_le _ _ hl
    let j : PUnit → D.t.PP.L.ι := fun _ => l
    have hV : z ∈ (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i := ⟨mem_pull.2 hU, hi⟩
    have hle : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U l := fun _ hy => mem_pull.1 hy.1
    have h1 := mem_basicOpen_appLE D.m.φ hle _ hV hl
    have e := hcompat j i hle
    refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
    change z ∈ D.tK.G.left.basicOpen ((D.m.φ.appLE _ _ hle).hom _) at h1
    rw [e, Scheme.basicOpen_mul] at h1
    exact ((mem_basicOpen_map _ _ z).1 h1.2).2
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  refine ⟨KeyBadModel.keyInOf D.tK xth D.g hg v' hv' ⟨inferInstance, sm, hp, gc⟩ hd
    (fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩) ha hk hne, GlobalTheory.GeneratorFrame.ofPow s, rfl,
    fun i => tanVec D.MB (e i), sameSec_ofPow s, hnv, ?_, hv, fun i => tanVec_left _ _⟩
  have he : eSec D.tK.G ≫ D.m.φ = spMap (algebraMap (𝓞 L) L) ≫ eSec D.t.G := by
    have := D.m.cm.e_comm
    rwa [D.m.base] at this
  have hrig : ∀ (e' : (𝟙_ (Over (Sp L))).left ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left) (he' : eSec D.tK.G ≫ D.m.φ = e' ≫ eSec D.t.G),
      e' = D.m.cm.e → rigPullOf D.m.φ e' he' D.t.PP.L D.t.PP.rig = D.m.cm.rigPull D.t.PP.L D.t.PP.rig := by
    rintro _ _ rfl
    rfl
  refine ⟨D.m.φ, he, w, D.m.cart, hw, ?_, hcompat, fun i => ?_⟩
  · have h2 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.tK.G) (fun _ => 1)) D.tK.PP.rig
        (rigPullOf D.m.φ (spMap (algebraMap (𝓞 L) L)) he D.t.PP.L D.t.PP.rig) := by
      rw [hrig _ he D.m.base.symm]
      exact hr
    exact h2
  · exact (hφ i).trans (by rw [dualMapR_eq])

end Main

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum
end
end
