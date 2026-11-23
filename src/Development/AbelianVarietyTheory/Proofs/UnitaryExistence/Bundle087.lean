module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle063
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_isSplit_period_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty hc i
  have hp : (F.Di i).p = D.p := (F.sig i).1
  have hq : (F.Di i).q = D.q := (F.sig i).2
  refine exists_isSplit_of_splitLat E H (F.Di i) g ty (by rw [hp, hq]; exact hty) ?_
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact splitLat_of_definite E H (F.Di i) (by rw [hp, hq]; exact h0)
  · have h1 : D.p ≠ 0 := fun h => h0 (Or.inl h)
    have h2 : D.q ≠ 0 := fun h => h0 (Or.inr h)
    rcases hc with h | h | ⟨h3, h4⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact GlobalTheory.SplitGenus.splitLat_of_indefinite E H (F.Di i) h4 (by omega) (by omega) (by omega)

end GlobalTheory.CompRat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem univFrame_borelPairs : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  intro hS E _ _ _ H Dw l Xo c p A j y₀ π X s u hj hU
  obtain ⟨B, q, Y, r, hYd, hYz, hY⟩ := GlobalTheory.T.exists_triangularFrameRing_over_testRing c.F (E →+* ℂ) (fun τ => Dw.mult τ) A
  obtain ⟨uB, huB⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A.R B.R q u
  obtain ⟨uB', huB', -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c B.R uB Y r
    fun τ => lowerTri_isUnit_det _ (hYz τ) (hYd τ)
  have hux : u.x = spMap π.toRingHom ≫ y₀.x := by
    obtain ⟨-, u₀, h₀, h₁⟩ := hU
    exact h₁.1.trans h₀.1
  have hx' : uB'.x = spMap (q.comp π).toRingHom ≫ y₀.x := by
    rw [huB'.1, huB.1, hux, spMap_algHom_comp, Category.assoc]
  obtain ⟨q', ⟨-, hq'⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c p.R A.R y₀ π X s u hU B.R uB' (q.comp π) hx'
  refine ⟨B, uB, uB', fun k => match k with
    | none => r
    | some ⟨τ, i⟩ => (hYd τ i).unit, q, q', huB, hq',
    (frBor_iff_frChg uB uB' _).2 ⟨Y, hYz, fun τ i => (hYd τ i).unit_spec.symm, huB'⟩, ?_⟩
  intro T _ _ a a' z z' t hz hz' hb
  obtain ⟨g, hgz, hgd, hgc⟩ := (frBor_iff_frChg z z' t).1 hb
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, -⟩ := hY T a g (t none)
    (fun τ i => by rw [hgd]; exact Units.isUnit _) hgz
  have h1 : FrMap b uB z :=
    frMap_cancel (Xo := Xo) (c := c) _ _ _ q b u uB z huB (by rw [hb1]; exact hz)
  have h2 : FrMap b uB' z' := by
    refine (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c B.R T b uB uB' z z' Y r huB' h1).2 ?_
    rw [hb3, funext hb2]
    exact hgc
  have h3 : FrMap (b.comp q') u z' := frMap_trans (Xo := Xo) (c := c) _ _ _ q' b u uB' z' hq' h2
  refine ⟨b, hb1, GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hU T _ _ z' h3 hz', ?_⟩
  rintro (_ | ⟨τ, i⟩)
  · exact hb3
  · show b (Y τ i i) = _
    rw [← hgd, ← hb2 τ]
    rfl

end GlobalTheory.Frames
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_sabMap_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} (T : CDVR) {x x' : Sp T.Fr ⟶ Xo.X} (hx : x' = x) (G G₂ : SAB H (Sp T.V))
    (t t₂ : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr)))
    (n₁ : SABMap t₂ Xo.univ.t x') (n₂ : SABMap t₂ G₂ (spMap (algebraMap T.V T.Fr))) :
    ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  subst hx
  exact GlobalTheory.T.semiAbelian_dvr_extensions_iso_compatible E H Dw l Xo T.V T.Fr x' G G₂ t t₂ m₁ m₂ n₁ n₂

theorem intLatU_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  intro E _ _ _ H Dw l Xo c T io y y'
  let := io.toAlgebra
  intro hx
  obtain ⟨G, t, m₁, m₂, ⟨ub, hub⟩, θ, hθ⟩ := y.2.2
  obtain ⟨G₂, t₂, n₁, n₂, ⟨ub₂, hub₂⟩, θ₂, hθ₂⟩ := y'.2.2
  obtain ⟨k, n, hk, hn⟩ := exists_sabMap_of_eq T hx G G₂ t t₂ m₁ m₂ n₁ n₂
  refine ⟨GlobalTheory.T.integral_frames_differ_by_unit' E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn ub ub₂ hub hub₂, ?_⟩
  intro a pm h1 h2 h3
  refine GlobalTheory.T.valV_eq_one_integral_generators E H Dw l Xo c T io y.1 y'.1 G G₂ t t₂ m₁ m₂ n₁ n₂ k n hx hk hn θ θ₂ hθ hθ₂ a
    ⟨pm, h1, ?_, h3⟩
  have hid : spMap (RingHom.id T.Fr) = 𝟙 (Sp T.Fr) := Spec.map_id _
  rw [h2, hid]
  exact (Category.comp_id _).symm

end GlobalTheory.Frames
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.exists_unitaryAdelicChar_of_heckeChar : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  first | exact @GlobalTheory.Member.exists_muVal | exact GlobalTheory.Member.exists_muVal | (intros; apply GlobalTheory.Member.exists_muVal <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.ExpClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))

theorem expUniq : ExpUniq e F := by
  intro i P P' hP hP' gam h hEF hM hA hrel z
  have hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z :=
    fun z => LinearMap.toMatrix'_mulVec _ z
  have key := @GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam
    (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)
  have := key.2.2 z
  rwa [hm] at this

theorem expLin : ExpLin e F := by
  intro i P hP m w vs cf v hvs hv
  exact (@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv

theorem expTan : ExpTan e F := by
  intro i P hP w v hv
  refine ⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩
  refine (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
  · exact absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'

theorem lieEig : LieEig e F := by
  intro i P hP τ v hv he
  obtain ⟨w, hw, -⟩ := (@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv
  have hs := (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he
  refine ⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩
  have hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w := by
    funext k
    obtain ⟨⟨τ', m⟩, rfl⟩ := e.symm.surjective k
    by_cases hτ : τ' = τ
    · subst hτ
      exact sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m
    · have h0 : w (e.symm ⟨τ', m⟩) = 0 := by
        by_contra hne
        have := hs _ hne
        rw [Equiv.apply_symm_apply] at this
        exact hτ this
      rw [h0]
      simp [Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]
  rw [hsum]
  exact hw

end GlobalTheory.ExpClauses

theorem GlobalTheory.exp_four_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), ExpUniq e F ∧ ExpLin e F ∧ ExpTan e F ∧ LieEig e F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ e F =>
    ⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

namespace GlobalTheory.AbelianSubgroupFinite

theorem finite_points_of_isOpenImmersion {k : Type} [Field k] [IsAlgClosed k]
    (N : Over (Sp k)) [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    {N₀ : Over (Sp k)} (ν : N₀ ⟶ N) [IsOpenImmersion ν.left] (e : 𝟙_ (Over (Sp k)) ⟶ N₀)
    (he : e ≫ ν = η[N]) [Finite (𝟙_ (Over (Sp k)) ⟶ N₀)] : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  let φ : (𝟙_ (Over (Sp k)) ⟶ N) → (N₀ ⟶ N) := fun x => ν ≫ (GrpObj.mulRight x).hom
  have hφ : ∀ x, IsOpenImmersion (φ x).left := fun x => by
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    simp only [φ, Over.comp_left]
    infer_instance
  have hx : ∀ x, e ≫ φ x = x := fun x => by
    simp only [φ]
    rw [← Category.assoc, he]
    simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_finite_subcover
    (fun x => Set.range (φ x).left) (fun x => (φ x).left.isOpenEmbedding.isOpen_range) (by
      rintro _ ⟨x, rfl⟩
      refine Set.mem_iUnion.2 ⟨x, e.left pt, ?_⟩
      simp only [F]
      conv_rhs => rw [← hx x]
      simp only [Over.comp_left, Scheme.Hom.comp_apply])
  refine Finite.of_surjective
    (fun p : t × (𝟙_ (Over (Sp k)) ⟶ N₀) => p.2 ≫ φ p.1.1) fun y => ?_
  obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht ⟨y, rfl⟩)
  have hsub : Set.range y.left ⊆ Set.range (φ x).left := by
    rintro _ ⟨a, rfl⟩
    have : Subsingleton (Sp k) := inferInstance
    rw [show a = pt from this.elim _ _]
    exact hy
  refine ⟨⟨⟨x, hxt⟩, Over.homMk (IsOpenImmersion.lift (φ x).left y.left hsub) ?_⟩, ?_⟩
  · rw [← (φ x).w, IsOpenImmersion.lift_fac_assoc, y.w]
  · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac (φ x).left y.left hsub)

theorem finite_of_torsionFree : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) := by
  intro k _ _ B _ n hB hn hnk C Z hZ hC htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have hfin₀ : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine GlobalTheory.T.finite_points_abelianVariety_of_no_torsion k N₀ hA n hn.two_le hnk fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  have := finite_points_of_isOpenImmersion N ν₀ η[N₀] (IsMonHom.one_hom ν₀)
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  obtain ⟨l, hl⟩ := exists_lift_of_range_subset x.left ν.left (hr ▸ (hC x).1 hx)
  refine ⟨Over.homMk l ?_, Subtype.ext (Over.OverMorphism.ext hl)⟩
  rw [← ν.w, ← Category.assoc, hl, x.w]

end GlobalTheory.AbelianSubgroupFinite
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem _root_.GlobalTheory.T.exists_integralFrames_model_invertible_pushforward : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntFramesSt Xo c := by
  first | exact @GlobalTheory.intFrames_of_laws | exact GlobalTheory.intFrames_of_laws | (intros; apply GlobalTheory.intFrames_of_laws <;> assumption)
end
