module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle164
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle044
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralJetBasis
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatGenFrameIndependent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle166
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle167
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.torus_split_pullback_generic : ∀ (X Z' : Scheme.{0}) (G : Over X) [GrpObj G] (G' : Over Z') [GrpObj G'] (ρ : Z' ⟶ X)
    (Φ : G'.left ⟶ G.left), IsGrpPullback G' G ρ Φ → ∀ (Xc : Type) [AddCommGroup Xc] [Module.Free ℤ Xc] [Module.Finite ℤ Xc]
    (u : splitTorus Z' Xc ⟶ G') [IsMonHom u] (L k : Type) [Field L] [Field k] [Algebra L k] (x : Sp k ⟶ Z') (zL : Sp L ⟶ X),
    x ≫ ρ = spMap (algebraMap L k) ≫ zL → ∀ (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left),
    IsGrpPullback GK G zL φ → ∀ τ : TorusExtension GK,
    (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc), t ≫ u = 1 → t = 1) →
    (∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ' : TorusExtension Gk,
      letI := τ'.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk),
        p ≫ τ'.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' Xc, (t ≫ u).left = p.left ≫ ψ) →
    letI := τ.addCommGroup
    ∃ e : τ.X ≃+ Xc, ∀ (A : Type) [CommRing A] (g : k →+* A) (b : Sp A ⟶ Z') (_ : spMap g ≫ x = b) (b' : Sp A ⟶ Sp L)
      (_ : spMap (g.comp (algebraMap L k)) = b') (t : Over.mk b ⟶ splitTorus Z' Xc) (t' : Over.mk b' ⟶ splitTorus (Sp L) τ.X),
      (∀ χ, charVal t' χ = charVal t (e χ)) → (t ≫ u).left ≫ Φ = (t' ≫ τ.i).left ≫ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_stratum_cocharacters_compare <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsClosed

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem exists_transport (u : splitTorus S X ⟶ G) {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (e : a = a')
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk a' ⟶ splitTorus S X, (∀ χ, charVal t' χ = charVal t χ) ∧ (t' ≫ u = 1 → t ≫ u = 1) := by
  subst e
  exact ⟨t, fun _ => rfl, id⟩

theorem killsOver_comp (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B B' : Type} [CommRing B] [CommRing B']
    (b : Sp B ⟶ S) (c : B →+* B') (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  have e : spMap g ≫ spMap c ≫ b = spMap (g.comp c) ≫ b := by
    rw [← Category.assoc, spMap_comp_eq]
  obtain ⟨t', h1, h2⟩ := exists_transport u e t
  exact h2 (h A (g.comp c) t' fun y hy => by rw [h1]; exact ht y hy)

theorem killsOver_pow (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) {R : Type} [CommRing R]
    [IsLocalRing R] (b : Sp R ⟶ S) (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) (n : ℕ) :
    KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b) := by
  induction n with
  | zero =>
    let c : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha))
    have hc : c.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext x; rfl
    have key := killsOver_comp u Y _ c h
    rw [← Category.assoc, spMap_comp_eq, hc] at key
    exact key
  | succ n ih =>
    have hJ : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≠ ⊤ := by
      intro e
      have h1 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R :=
        Ideal.pow_le_self (by omega)
      rw [e] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h1)
    haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 hJ
    haveI : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _)
    have hI : I ^ 2 = ⊥ := by
      simp only [I]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    refine GlobalTheory.T.killsOver_square_zero_lift S G X u Y _ _ I hI ?_
    let c : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)) →+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
    have hc : c.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _) := by
      ext x; rfl
    have key := killsOver_comp u Y _ c ih
    rw [← Category.assoc, spMap_comp_eq, hc, ← spMap_comp_eq, Category.assoc] at key
    exact key

theorem diff_injective_mod_pi : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro R K _ _ _ _ _ _ S b G _ _ X _ _ u _ hK M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := GlobalTheory.T.torus_kernel_prime_quotient S G X u (IsLocalRing.ResidueField R)
    (spMap (IsLocalRing.residue R) ≫ b) M hM δ hne hδ
  have hR := GlobalTheory.T.killsOver_of_adic_completion S G X u ψ.ker R b (killsOver_pow u ψ.ker b hk)
  have hKk := killsOver_comp u ψ.ker b (algebraMap R K) hR
  haveI := Fact.mk hl
  obtain ⟨-, -, h1, -, hex, -⟩ := GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra K (ZMod l))
    (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ spMap (algebraMap R K) ≫ b)
  let w : Multiplicative X →* AddMonoidAlgebra K (ZMod l) :=
    (AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)
  obtain ⟨t, ht⟩ := hex w
  have hu : t ≫ u = 1 := hKk _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t fun y hy => by
    rw [ht]
    have hy0 : ψ y = 0 := hy
    simp [w, hy0, AddMonoidAlgebra.one_def]
  have ht1 := hK _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t hu
  obtain ⟨χ, hχ⟩ := hψ 1
  have key := ht χ
  rw [ht1, h1] at key
  simp only [w, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, hχ] at key
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_left_inj one_ne_zero] at key
  exact zero_ne_one key

end GlobalTheory.CompanionTheory.Ar.TsClosed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.uniformised_eigen_frame_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anSolve | exact GlobalTheory.CompanionTheory.Ar.Flat.anSolve | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anSolve <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.holomorphic_endomorphism_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | exact GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.exists_sqrt_neg_disc_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | exact GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PointDet.detCond_at_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

theorem _root_.GlobalTheory.T.flat_gen_frame_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ φ₀ : FrameFn Xo c) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → IsFlatGen U τ φ FU i → IsFlatGen U τ φ₀ FU i → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → ∃ a : ℂ, ∀ y v w, IsFramed U τ (algebraMap c.F ℂ) y v w → φ ℂ y v w = a * φ₀ ℂ y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex | exact GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.flatGen_ratio_complex <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_cpt_birational_arith_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.flagged_model_dim | exact GlobalTheory.CompanionTheory.Ar.flagged_model_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.flagged_model_dim <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_model_point_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG :=
  PositivityTheory.HtPt.Gh.hodge_tate_free_sandwich

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.complex_abelian_fibre_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | exact GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.exists_integral_jet_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (n r : ℕ) (s : Fin r → Out.H0 D.t.PP.L n), ∃ J : ℕ → Fin r → L, (∀ (i : ℕ) (c : Fin r → 𝓞 L), (∀ k < i, ∑ j, (c j : L) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : L) * J i j)) ∧ ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ), (∀ j, a.IsFn (s j) (f j)) → D.IsVec a x v → ∀ (i : ℕ) (c : Fin r → ℂ), ((∀ k < i, ∑ j, c j * σ (J k j) = 0) ↔ ∀ k < i, iteratedDeriv k (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0 = 0) ∧ ((∀ k < i, ∑ j, c j * σ (J k j) = 0) → ∑ j, c j * σ (J i j) = iteratedDeriv i (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.JetMain.jets | exact GlobalTheory.CompanionTheory.Ar.JetMain.jets | (intros; apply GlobalTheory.CompanionTheory.Ar.JetMain.jets <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.transition_matrix_period_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (ρ : ℂ), LinearIndependent (𝓞 E) e → IsTransition (FU.Di i) x e T → T.det ≠ 0 → IsConstMul U τ φ FU i e ρ → IsConstMul U τ φ FU i x (ρ / τ T.det) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.constMul_change_generator | exact GlobalTheory.CompanionTheory.Ar.Fl.constMul_change_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.constMul_change_generator <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formal_germ_jet_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv (R := k) q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | exact GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | (intros; apply GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion <;> assumption)
end
