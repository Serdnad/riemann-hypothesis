module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle150
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle044
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle168
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle169
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.derivation_vanishing_constants : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom → ∀ (V : G.left.Opens), IsAffineOpen V → ⊤ ≤ (1 : Over.mk (spMap φ) ⟶ G).left ⁻¹ᵁ V →
  ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V r) = 0) →
    (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f * D f' + valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f' * D f) →
    ∃! c : Fin g → ℂ, ∀ f, D f = ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left) V f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev sqU : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G ⊗ t.G :=
  lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))

theorem sqPt_left_fst (a : t.G ⊗ t.G ⟶ t.G) :
    (sqPt t x a).left ≫ pullback.fst t.G.hom x = sqMap t x ≫ a.left :=
  pullback.lift_fst _ _ _

theorem fib_ext {T : Over (Sp k)} {a b : T ⟶ GF t x}
    (h : a.left ≫ pullback.fst t.G.hom x = b.left ≫ pullback.fst t.G.hom x) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem sqPt_psum {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (I : Finset (Fin n)) :
    sqPt t x (psum t.G xs I) = psum (GF t x) (fun i => sqPt t x (xs i)) I := by
  apply fib_ext
  rw [sqPt_left_fst]
  refine Eq.symm (psum_push (isGrpPullback_pullback t.G x) _ xs (sqU t x) (fun i => ?_) I)
  apply Over.OverMorphism.ext
  exact sqPt_left_fst t x (xs i)

theorem sqPt_fst : sqPt t x (fst t.G t.G) = fst (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ fst t.G t.G).left = _
  rw [lift_fst]
  rfl

theorem sqPt_snd : sqPt t x (snd t.G t.G) = snd (GF t x) (GF t x) := by
  apply fib_ext
  rw [sqPt_left_fst]
  show (sqU t x ≫ snd t.G t.G).left = _
  rw [lift_snd]
  rfl

theorem sqPt_comp (b : t.G ⊗ t.G ⟶ t.G) (c : t.G ⟶ t.G) :
    sqPt t x (b ≫ c) = sqPt t x b ≫ (Over.pullback x).map c := by
  apply fib_ext
  rw [sqPt_left_fst, Over.comp_left, Over.comp_left, Category.assoc]
  have A : ((Over.pullback x).map c).left ≫ pullback.fst t.G.hom x = pullback.fst t.G.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  rw [A, ← Category.assoc (Over.Hom.left (sqPt t x b)), sqPt_left_fst]
  simp only [Category.assoc]

theorem psum_comp_hom {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] {T : Over S} {n : ℕ} (ys : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    psum A ys I ≫ q = psum B (fun i => ys i ≫ q) I :=
  psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) ys I

theorem comp_psum {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {T T' : Over S} (U : T' ⟶ T) {n : ℕ} (ys : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    U ≫ psum B ys I = psum B (fun i => U ≫ ys i) I :=
  psum_hom (preHom U) ys I

section Quot

variable {t x} (Q : AbQuot t x)

abbrev qL : GF t x ⊗ GF t x ⟶ Q.tB.G ⊗ Q.tB.G :=
  lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)

theorem sqPt_psum_q {n : ℕ} (xs : Fin n → (t.G ⊗ t.G ⟶ t.G)) (ys : Fin n → (Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G))
    (h : ∀ i, sqPt t x (xs i) ≫ Q.q = qL Q ≫ ys i) (I : Finset (Fin n)) :
    (sqPt t x (psum t.G xs I)).left ≫ Q.q.left = qq Q ≫ (psum Q.tB.G ys I).left := by
  haveI := Q.q_hom
  have e : sqPt t x (psum t.G xs I) ≫ Q.q = qL Q ≫ psum Q.tB.G ys I := by
    rw [sqPt_psum, psum_comp_hom, comp_psum]
    exact congrArg (fun z => psum Q.tB.G z I) (funext h)
  exact congrArg (fun z => z.left) e

theorem sqPt_fst_q : sqPt t x (fst t.G t.G) ≫ Q.q = qL Q ≫ fst Q.tB.G Q.tB.G := by
  rw [sqPt_fst, lift_fst]

theorem sqPt_snd_q : sqPt t x (snd t.G t.G) ≫ Q.q = qL Q ≫ snd Q.tB.G Q.tB.G := by
  rw [sqPt_snd, lift_snd]

theorem sqPt_act_q {b : t.G ⊗ t.G ⟶ t.G} {b' : Q.tB.G ⊗ Q.tB.G ⟶ Q.tB.G}
    (h : sqPt t x b ≫ Q.q = qL Q ≫ b') (a : 𝓞 E) :
    sqPt t x (b ≫ t.act.act a) ≫ Q.q = qL Q ≫ b' ≫ Q.tB.act.act a := by
  rw [sqPt_comp, Category.assoc, Q.act_q, ← Category.assoc, h, Category.assoc]

end Quot

theorem adF_fst (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ pullback.fst t.G.hom x = sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i := by
  rcases i with I | I
  · exact sqPt_left_fst t x _
  · exact sqPt_left_fst t x _

theorem adF_q {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) (a : 𝓞 E) (i : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2))) :
    adF t x a i ≫ Q.q.left = qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)])
      (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i := by
  rcases i with I | I
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_fst_q Q
    · exact sqPt_act_q Q (sqPt_snd_q Q) _
  · refine sqPt_psum_q Q _ _ (fun i => ?_) I.down
    fin_cases i
    · exact sqPt_act_q Q (sqPt_fst_q Q) _
    · exact sqPt_snd_q Q

theorem adjunction_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → ∃ u : Γ((GF t x ⊗ GF t x).left, ⊤)ˣ, Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) u := by
  intro E _ _ _ H _ _ X t k _ _ p _ _ x Q d d' g gB w hw a wL wB hL hB
  exact GlobalTheory.T.generator_ratio_unit_exists t.G.left Q.tB.G.left (GF t x).left t.PP.L Q.tB.PP.L (pullback.fst t.G.hom x) Q.q.left
    t.PP.isLB Q.tB.PP.isLB w hw _ _ (adF t x a) _ _ _ _ _ (adF_fst t x a) (adF_q Q a)
    (LB.isGen_pullGen _ _ _ _ hL _) (LB.isGen_pullGen _ _ _ _ hB _)

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdTr
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GP

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_coeff {r : ℕ} (b b₀ : Fin r → E) (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i)
    (hli : LinearIndependent Ω b) (i : Fin r) :
    ∃ t : Ω, t ≠ 0 ∧ b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i := by
  have hni : b i ∉ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := hli.notMem_span_image (by simp)
  have h1 : b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ (i+1) := by rw [← h]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [GlobalTheory.CompanionTheory.Ar.Flag.step_succ] at h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have ht : t ≠ 0 := by rintro rfl; apply hni; rw [h, ← hyz]; simpa using hy
  exact ⟨t, ht, by rw [← hyz]; simpa using hy⟩

theorem gr_isGen_of_frame (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ)
    (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) (hb : L.IsFrameAt b p) (i : Fin r) {t : Ω}
    (ht : t ≠ 0) (hy : b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p t := by
  refine ⟨ht, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro s ⟨e, he, hs⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have h2 : (∑ k, c k • b k) - (s / t) • b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := by
      rw [h]
      have : (∑ k, c k • b k) - (s / t) • b i =
          ((∑ k, c k • b k) - s • b₀ i) - (s / t) • (b i - t • b₀ i) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht]; abel
      rw [this]; exact sub_mem hs (Submodule.smul_mem _ _ hy)
    obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[Ω] Ω, ∀ k, φ (b k) = if k = i then 1 else 0 := by
      obtain ⟨g, hg⟩ := (Fintype.linearCombination Ω b).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro m hm; funext k; exact Fintype.linearIndependent_iff.1 hb.1 m (by simpa [Fintype.linearCombination_apply] using hm) k))
      refine ⟨(LinearMap.proj i).comp g, fun k => ?_⟩
      have := LinearMap.congr_fun hg (Pi.single k 1)
      simp [Fintype.linearCombination_apply_single] at this
      simp [this, Pi.single_apply, eq_comm]
    have h3 : GlobalTheory.CompanionTheory.Ar.flagStep Ω b i ≤ LinearMap.ker φ := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have : k ≠ i := by rintro rfl; simp at hk
      simp [hφ, this])
    have h4 := h3 h2
    have h5 : ∀ k, φ (c k • b k) = (c k : Ω) * φ (b k) := fun k => φ.map_smul (c k : Ω) (b k)

    simp only [LinearMap.mem_ker, map_sub, map_sum, h5, map_smul, hφ] at h4
    simp at h4
    refine Submodule.mem_span_singleton.2 ⟨c i, ?_⟩
    show (c i : Ω) * t = s
    rw [sub_eq_zero.1 h4, div_mul_cancel₀ _ ht]
  · rintro _ rfl
    exact ⟨b i, by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩, hy⟩

theorem gen_ratio {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    ∃ u : Ω, u ∈ regAt ξ p ∧ u⁻¹ ∈ regAt ξ p ∧ s = u * t := by
  have a1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self _
  have a2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs.2, ht.2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 a2
  have hu' : (u : Ω) * t = s := hu
  have hv' : (v : Ω) * s = t := hv
  have e : (v : Ω) * (u : Ω) = 1 := by
    refine mul_right_cancel₀ ht.1 ?_
    rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
  refine ⟨u, u.2, ?_, hu'.symm⟩
  rw [← eq_inv_of_mul_eq_one_left e]
  exact v.2

theorem gen_mul {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {t u : Ω} (h : Λ.IsGenAt p t) (h0 : u ≠ 0)
    (hu : u ∈ regAt ξ p) (hu' : u⁻¹ ∈ regAt ξ p) : Λ.IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero h0 h.1, ?_⟩
  rw [h.2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u⁻¹, hu'⟩, inv_mul_cancel_left₀ h0 _⟩
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

end Frames

section Pull

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {E E₀ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₀] [Module Ω₀ E₀]

theorem mem_flagStep_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {y : Fin r → E₀} {n : ℕ} {x : E₀} (hx : x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    j x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_pull_le {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {x y : Fin r → E₀} {n : ℕ} (h : GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ x n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (x k)) n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_flagStep_pull hj (h (Submodule.subset_span ⟨k, hk, rfl⟩))

theorem isFrameAt_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀))) {r : ℕ} {b : Fin r → E₀}
    (hb : L₀.IsFrameAt b p₀) : L.IsFrameAt (fun k => j (b k)) p := by
  refine ⟨hli _ _ hb.1, ?_⟩
  rw [hL]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ L₀ p₀ := he
    rw [hb.2] at he'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'

    rw [map_sum]
    refine sum_mem fun k _ => ?_
    have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ p) • j (b k) := hj (c k : Ω₀) (b k)
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    refine ⟨b k, ?_, rfl⟩
    show b k ∈ L₀ p₀
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem isGenAt_pull (i : Ω₀ →+* Ω) (j : E₀ →+ E) {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    {r : ℕ} {c₀ : Fin r → E₀} {c : Fin r → E} (hc : ∀ a, j (c₀ a) = c a)
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀)))
    (hf : L₀.IsFlagVBOn Set.univ c₀) (a : Fin r) {t₀ : Ω₀} (h : (L₀.gr c₀ a).IsGenAt p₀ t₀) :
    (L.gr c a).IsGenAt p (i t₀) := by
  obtain ⟨U, hU, b₁, hb, hfr⟩ := hf p₀ trivial
  have hfr' := hfr p₀ trivial hU
  obtain ⟨t₁, ht₁, hy⟩ := exists_coeff b₁ c₀ hb hfr'.1 a
  have g₁ := gr_isGen_of_frame L₀ b₁ c₀ p₀ hb hfr' a ht₁ hy
  obtain ⟨u, hu, hu', rfl⟩ := gen_ratio h g₁
  have hc' : c = fun k => j (c₀ k) := funext fun a => (hc a).symm
  subst hc'
  have hframe : L.IsFrameAt (fun k => j (b₁ k)) p := isFrameAt_pull hreg hj hli hL hfr'
  have hadapt : ∀ n, GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (b₁ k)) n = GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) n :=
    fun n => le_antisymm (flagStep_pull_le hj (hb n).le) (flagStep_pull_le hj (hb n).ge)
  have hy' : j (b₁ a) - i t₁ • j (c₀ a) ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) a := by
    have := mem_flagStep_pull hj hy
    rwa [map_sub, hj] at this
  have g := gr_isGen_of_frame L (fun k => j (b₁ k)) (fun k => j (c₀ k)) p hadapt hframe a
    ((map_ne_zero i).2 ht₁) hy'
  have hu0 : u ≠ 0 := left_ne_zero_of_mul h.1
  rw [map_mul]
  refine gen_mul g ((map_ne_zero i).2 hu0) (hreg _ hu) ?_
  rw [← map_inv₀]
  exact hreg _ hu'

end Pull

theorem genPull_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hr hj hli hb hV
  intro q hq s a t₀ hg
  exact isGenAt_pull i j (hr q) hj hli (hb s) (hV q hq s) (Fl₀.sub s) a hg

end GlobalTheory.CompanionTheory.Ar.Chg.GP
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_cokernel_sharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp :=
  PositivityTheory.HtPt.Farsharp.hodgeTateCokerSharp

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.hodge_comp_root_model_primes : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | exact GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.values_identity_power_relation : ∀ {C : Type} [CommRing C] (m N : ℕ) (T T' th sv d : C) (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : Cˣ), T' * ((Wk1 : C) * (R : C) ^ ((N * m) ^ 2)) = th ^ ((N * m) ^ 2) * (Wkz : C) → T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2) = sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2) → A = bo * (bz ^ (N ^ 2))⁻¹ * Wy → B = bo * (bo ^ (N ^ 2))⁻¹ * Wo → R = bo * R' → ((bz ^ (m ^ 2) : Cˣ) : C) * sv = d * (th * ((up⁻¹ : Cˣ) : C)) → Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ = Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹ → Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2) → u0 = e0 * (R ^ (m ^ 2))⁻¹ → e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1 → T ^ (m ^ 2) = d ^ ((N * m) ^ 2) * T' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.tensor_wedge_det_change : ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (V : Ψ → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)] (n : ℕ) (e e' : ∀ τ, Fin n → V τ) (T : ∀ τ, Matrix (Fin n) (Fin n) Ω) (a a' : Ω), (∀ τ, LinearIndependent Ω (e τ)) → (∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤) → (∀ τ q, e' τ q = ∑ p, T τ p q • e τ p) → a • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) = a' • (PiTensorProduct.tprod Ω fun τ => exteriorPower.ιMulti Ω n (e' τ) : PiTensorProduct Ω fun τ => ⋀[Ω]^n (V τ)) → a = a' * ∏ τ, (T τ).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det | exact GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det | (intros; apply GlobalTheory.CompanionTheory.Ar.TopWedge.eq_mul_prod_det <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  intro K _ J _ Ω _ _ y c hc R _ θ hθ F hF S hS
  exact exists_hom_adjoin_inv (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)
    (θ.comp (map (algebraMap ℚ ℂ)))
    (fun G hG => hθ _ (GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal K J Ω y c hc G hG)) F hF S hS

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem _root_.GlobalTheory.T.rational_relation_in_chart_ideal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal | exact GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal <;> assumption)
end
