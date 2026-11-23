module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle683
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2671
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RefTauCoord

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem gm_stalk {X Y Z : Scheme.{0}} (κ : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ r) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm r (κ z) U a) := by
  apply Units.ext
  refine (gm_val (κ ≫ r) z U h a).trans (Eq.trans ?_ (congrArg (κ.stalkMap z).hom (gm_val r (κ z) U h a)).symm)
  exact (Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) z h _).symm

theorem val_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : Z ⟶ Y) (r : Y ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    val t (κ ≫ r) z J = Units.map (κ.stalkMap z).hom.toMonoidHom (val t r (κ z) fun ψ => J (κ ≫ ψ)) := by
  rw [val_of t (κ ≫ r) z J (fun k => J (κ ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_stalk κ r z _ (Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)) _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem exists_good_over (ξ : Spec (CommRingCat.of (FractionRing R))) {X S : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ S) [IsSeparated s] (f : Spec (CommRingCat.of R) ⟶ S) :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of R) ⟶ X, p ≫ s = f →
      p (closedPoint R) ∈ L.U (J (jK R ≫ p)) := by
  haveI : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ X => exists_chart hL (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of R) ⟶ X // p ≫ s = f})
    (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK R) h))
    (fun p => by
      have := DVR.eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK R ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem gm_unitOn {A : Type} [CommRing A] (σ : A →+* FractionRing R) (ξ : Spec (CommRingCat.of (FractionRing R)))
    (k : Aˣ) : (gm (spMap σ) ξ ⊤ (unitOn k)).val = kst ξ (σ k) := by
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) k.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  exact (congrArg ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ ξ trivial).hom hnat).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (hρ : Function.Injective ρ),
    Refines Q ρ D e → ∀ (a b : D.X) (k : (FractionRing R)ˣ), Q.TauCoord (e a) (e b) k →
      ∀ x : (FractionRing R')ˣ, IsTauCoord D a b x → ∃ u : R'ˣ, (x : FractionRing R') =
        algebraMap R' (FractionRing R') u * IsFractionRing.lift (A := R) (K := FractionRing R)
          (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) := by
  intro R _ _ R' _ _ _ Q ρ D e hρ href a b k hk x hx
  letI := D.P.isAb.comm
  obtain ⟨β, β₂, w, h₁, h₂, -, -, h₅⟩ := href
  have hσ : ∀ r, IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) r) =
      algebraMap R' (FractionRing R') (ρ r) := fun r => IsFractionRing.lift_algebraMap _ r
  generalize IsFractionRing.lift (A := R) (K := FractionRing R) (g := (algebraMap R' (FractionRing R')).comp ρ)
      ((IsFractionRing.injective R' (FractionRing R')).comp hρ) = σ at hσ ⊢
  have hκ : spMap σ ≫ jK R = jK R' ≫ spMap ρ := by
    have : σ.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp ρ := RingHom.ext hσ
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R'))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  obtain ⟨J, hJ, hc⟩ := exists_good_over ξ Q.M.isLB Q.B.hom (spMap ρ)
  have E := h₅ (spMap σ) hκ a b ξ J J' hJ hJ'
  obtain ⟨u₁, e₁⟩ := GlobalTheory.TauShift.coord_val D ξ hJ' hc' hx
  obtain ⟨u₂, e₂⟩ : ∃ u : R'ˣ, (lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left ξ J J').val =
      cst ξ u := by
    have hp : (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left = jK R' ≫ (lift (D.c a) (D.c b)).left := by
      simp [← CartesianMonoidalCategory.comp_lift]
    rw [hp]
    refine unit_gm' ξ (lift (D.c a) (D.c b)).left _ ?_ _
    refine And.intro (mem_pull.2 (Set.mem_iInter.2 fun I => ?_)) (Set.mem_iInter.2 fun I => ?_)
    · have := hc ((lift (D.c a) (D.c b)).left ≫ β₂ ≫ (psum Q.B (x2 Q.B) I.down).left) (by
        rw [Category.assoc, Category.assoc, Over.w, ← Over.w (fst Q.B Q.B), reassoc_of% h₂.1, h₁.1.w,
          Over.w_assoc, Over.w_assoc]
        exact Category.id_comp _)
      exact this
    · have := hc' ((lift (D.c a) (D.c b)).left ≫ (psum D.P.A (x2 D.P.A) I.down).left) (by
        rw [Category.assoc, Over.w, Over.w]; rfl)
      exact this
  obtain ⟨u, -, hu⟩ := hk
  obtain ⟨u₃, e₃⟩ : ∃ v : R'ˣ, (val u (jK R' ≫ spMap ρ) ξ J).val = cst ξ v := by
    refine unit_gm' ξ _ _ (Set.mem_iInter.2 fun i => ?_) _
    obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B, lamPts (Q.c (e a)) (Q.c (e b)) i = q.left := by
      fin_cases i <;> exact ⟨_, rfl⟩
    have := hc (spMap ρ ≫ lamPts (Q.c (e a)) (Q.c (e b)) i) (by
      rw [hq, Category.assoc, Over.w q]; exact Category.comp_id _)
    exact this
  have hT := congrArg (Units.map ((spMap σ).stalkMap ξ).hom.toMonoidHom)
    (hu (spMap σ ξ) (fun ψ => J (spMap σ ≫ ψ)) fun ψ => hJ (spMap σ ≫ ψ))
  have v₁ := val_stalk (Q.tau (e a) (e b)) (spMap σ) (𝟙 (TK R).left) ξ hJ
  have v₂ := val_stalk u (spMap σ) (toUnit (TK R)).left ξ hJ
  have v₃ := gm_stalk (spMap σ) (𝟙 (TK R).left) ξ ⊤ trivial (unitOn k)
  have hh : spMap σ ≫ (toUnit (TK R)).left = jK R' ≫ spMap ρ := by
    rw [show (toUnit (TK R)).left = jK R by simpa using Over.w (toUnit (TK R))]; exact hκ
  have hT' := v₁.trans (hT.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) v₃.symm v₂.symm)))
  rw [hh] at hT'
  rw [show spMap σ ≫ 𝟙 (TK R).left = spMap σ from Category.comp_id _] at hT'
  have F : (val (Q.tau (e a) (e b)) (spMap σ) ξ J).val = kst ξ (σ k) * cst ξ u₃ :=
    (congrArg Units.val hT').trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) (gm_unitOn σ ξ k) e₃))
  have G : kst ξ x.val = cst ξ u₁ * (cst ξ u₂ * (kst ξ (σ k) * cst ξ u₃)) :=
    (congrArg Units.val e₁).trans ((Units.val_mul _ _).trans (congrArg (cst ξ u₁ * ·)
      ((congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) e₂ F)))))
  refine ⟨u₁ * u₂ * u₃, kst_injective ξ ?_⟩
  rw [G, map_mul, kst_algebraMap, Units.val_mul, Units.val_mul, map_mul, map_mul]
  ring

end GlobalTheory.RefTauCoord
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.FubiniStudyFrame

theorem exists_ne_zero_of_rel {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n N : ℕ}
    (σ : K →+* ℂ) (u : Fin n → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin n) (Fin N) K)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin n → ℂ) (hw : w ≠ 0)
    (hrel : ∀ lam : Fin n → K, ∑ k, lam k • u k = 0 → ∑ k, σ (lam k) * w k = 0)
    (hb : ∀ j, b j = ∑ k, c k j • u k) (hA : A.det ≠ 0) :
    ∃ a, ∑ k, (c.map σ * A) k a * w k ≠ 0 := by
  classical
  have hx : Matrix.vecMul w (c.map σ) ≠ 0 := by
    intro hx
    apply hw
    funext l
    set r := b.repr (u l)
    have hl : ∑ k, ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) • u k = 0 := by
      have e : ∑ k, (∑ j, c k j * r j) • u k = u l := by
        calc ∑ k, (∑ j, c k j * r j) • u k = ∑ j, r j • ∑ k, c k j • u k := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
          _ = ∑ j, r j • b j := by simp only [hb]
          _ = u l := b.sum_repr (u l)
      simp only [sub_smul, Finset.sum_sub_distrib, e, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    have h2 := hrel _ hl
    have h3 : ∀ j, ∑ k, w k * σ (c k j) = 0 := fun j => by
      have := congrFun hx j
      simpa [Matrix.vecMul, dotProduct] using this
    have h4 : ∑ k, σ ((Pi.single l (1 : K) : Fin n → K) k - ∑ j, c k j * r j) * w k =
        w l - ∑ j, σ (r j) * ∑ k, w k * σ (c k j) := by

      simp only [map_sub, map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
      congr 1
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h2
    simpa [h3] using h2
  by_contra hne
  push_neg at hne
  have h0 : Matrix.vecMul (Matrix.vecMul w (c.map σ)) A = 0 := by
    rw [Matrix.vecMul_vecMul]
    funext a
    have := hne a
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact hA (Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hx, h0⟩)

theorem rel_field_of_rel_int {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {n : ℕ} (τ : 𝓞 K →+* ℂ) (u : Fin n → V)
    (w : Fin n → ℂ)
    (H : ∀ lam : Fin n → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0)
    (lam : Fin n → K) (h : ∑ k, lam k • u k = 0) :
    ∑ k, OfLattice.extEmb τ (lam k) * w k = 0 := by
  classical
  set σ := OfLattice.extEmb τ
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (𝓞 K)) (Finset.univ.image lam)
  have hk : ∀ k, IsLocalization.IsInteger (𝓞 K) (d • lam k) := fun k =>
    hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  choose lam' hlam' using hk
  have hσ : ∀ x : 𝓞 K, σ (algebraMap (𝓞 K) K x) = τ x := fun x =>
    RingHom.congr_fun (OfLattice.extEmb_comp τ) x
  have h1 : ∑ k, lam' k • u k = 0 := by
    have : ∀ k, lam' k • u k = d • (lam k • u k) := fun k => by
      rw [← algebraMap_smul K (lam' k) (u k), hlam' k, Algebra.smul_def, mul_smul,
        algebraMap_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h2 := H lam' h1
  have h3 : ∀ k, τ (lam' k) = σ (algebraMap (𝓞 K) K d) * σ (lam k) := fun k => by
    rw [← hσ, hlam' k, Algebra.smul_def, map_mul]
  simp only [h3, mul_assoc, ← Finset.mul_sum] at h2
  have hd0 : σ (algebraMap (𝓞 K) K d) ≠ 0 := by
    rw [map_ne_zero, ne_eq, ← map_zero (algebraMap (𝓞 K) K),
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero hd
  exact (mul_eq_zero.1 h2).resolve_left hd0

end GlobalTheory.FubiniStudyFrame


open GlobalTheory.FubiniStudyFrame in
theorem GlobalTheory.FubiniStudyFrame.noCommonZero_comb : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  intro K V _ _ _ _ _ _ m N X _ p g u b c A _hg hrel hb hA τ i y hy
  classical
  set s := fun k => GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g with hs
  set w : Fin (m + 1) → ℂ := fun k => secVal p τ (s k) i y with hw_def
  have hsup := ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  have hw : w ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y.1 (IsLocalRing.closedPoint ℂ) ∈ ⨆ k, nonzeroLocus (s k) by rw [hsup]; trivial)
    intro h0
    exact (secVal_ne_zero_iff (s k) hy).2 (mem_ptsIn.2 hk) (congrFun h0 k)
  have H : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, τ (lam k) * w k = 0 := by
    intro lam h
    have e := congrArg (fun t => secVal p τ t i y) (hrel lam h)

    simpa [map_sum, secVal_smul, Finset.sum_apply, hw_def] using e
  obtain ⟨a, ha⟩ := exists_ne_zero_of_rel (OfLattice.extEmb τ) u b c (A (OfLattice.extEmb τ)) w hw
    (rel_field_of_rel_int τ u w H) hb (hA _)
  refine ⟨a, ?_⟩
  simpa [Finset.sum_apply, hw_def] using ha
end

section

open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivBound

theorem exists_cdvr_valuation_le : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  intro V _ _ _ hV ν h1 h2 hm
  obtain ⟨-, -, -, h0⟩ := hV
  obtain ⟨m, hmm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hmK : algebraMap V (FractionRing V) m ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hm0
  haveI : ν.IsNontrivial := ⟨algebraMap V (FractionRing V) m, (ν.ne_zero_iff).2 hmK, (h2 m hmm).ne⟩
  haveI : IsDiscreteValuationRing ν.valuationSubring := inferInstance
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero ν.valuationSubring :=
    RingHom.charZero (algebraMap ν.valuationSubring (FractionRing V))
  obtain ⟨W', _, _, _, g, hW', hg, hgl⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding ν.valuationSubring
    inferInstance inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) inferInstance
  obtain ⟨hdvr, hc, hz⟩ := hW'

  let i : V →+* ν.valuationSubring := (algebraMap V (FractionRing V)).codRestrict ν.valuationSubring.toSubring (fun v => h1 v)
  have hi : ∀ v : V, ((i v : ν.valuationSubring) : FractionRing V) = algebraMap V (FractionRing V) v := fun _ => rfl
  have hiinj : Function.Injective i := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (by rw [← hi, ← hi, h])

  have hnu : ∀ w : ν.valuationSubring, ν (w : FractionRing V) < 1 → ¬ IsUnit w := fun w hw hu =>
    hw.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers ν)).mp hu)
  haveI hil : IsLocalHom i := ⟨fun a ha => by
    by_contra hna
    exact hnu (i a) (by rw [hi]; exact h2 a ((mem_maximalIdeal _).2 hna)) ha⟩
  haveI := hgl
  let g' : ν.valuationSubring →+* FractionRing W' := (algebraMap W' (FractionRing W')).comp g
  have hg' : Function.Injective g' :=
    (IsFractionRing.injective W' (FractionRing W')).comp hg
  let k : FractionRing V →+* FractionRing W' := IsFractionRing.lift (A := ν.valuationSubring) hg'
  have hk : ∀ w : ν.valuationSubring, k (w : FractionRing V) = algebraMap W' (FractionRing W') (g w) := fun w =>
    IsFractionRing.lift_algebraMap (A := ν.valuationSubring) hg' w
  refine ⟨W', inferInstance, inferInstance, inferInstance, hdvr, g.comp i, k, ⟨inferInstance, inferInstance, hc, hz⟩,
    hg.comp hiinj, inferInstance, fun v => by rw [← hi, hk]; rfl, ?_⟩
  rintro x y ⟨r, hr⟩
  by_cases hy : y = 0
  · have : k x = 0 := by rw [hr, hy, map_zero, mul_zero]
    rw [(map_eq_zero_iff k k.injective).1 this, hy]
  by_contra hxy
  rw [not_le] at hxy
  set z := x / y with hz'
  have hyν : ν y ≠ 0 := (ν.ne_zero_iff).2 hy
  have hz1 : 1 < ν z := by
    rw [hz', map_div₀]
    exact (one_lt_div₀ (zero_lt_iff.2 hyν)).2 hxy
  have hz0 : z ≠ 0 := by
    intro h; rw [h, map_zero] at hz1; exact not_lt_zero' hz1
  have hzi : ν z⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hz1
  let w : ν.valuationSubring := ⟨z⁻¹, hzi.le⟩
  have hkz : k z = algebraMap W' (FractionRing W') r := by
    rw [hz', map_div₀, hr, mul_div_assoc, div_self ((map_ne_zero k).2 hy), mul_one]
  have hkw : k (w : FractionRing V) = (k z)⁻¹ := by
    change k z⁻¹ = _
    rw [map_inv₀]
  rw [hk, hkz] at hkw
  have hunit : IsUnit (g w) := by
    have h : g w * r = 1 := by
      apply IsFractionRing.injective W' (FractionRing W')
      rw [map_mul, map_one, hkw, inv_mul_cancel₀]
      rw [← hkz]; exact (map_ne_zero k).2 hz0
    exact ⟨⟨g w, r, h, by rw [mul_comm]; exact h⟩, rfl⟩
  exact hnu w hzi (IsUnit.of_map g w hunit)

end GlobalTheory.DivBound
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelPointPairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hA : IsAbelianScheme A) {L : LB (G2 A).left} (hL : L.IsLB) {T : Over S} (a b c : T ⟶ G2 A) :
    pull (a * b * c).left (cls L hL) - pull (a * b).left (cls L hL) - pull (a * c).left (cls L hL)
      - pull (b * c).left (cls L hL) + pull a.left (cls L hL) + pull b.left (cls L hL) + pull c.left (cls L hL)
      - pull (1 : T ⟶ G2 A).left (cls L hL) = 0 := by
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨t, ht⟩ := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hA2 L hL T a b c
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_eight] at e
  simp at e
  rw [← e]
  abel


omit [IsCommMonObj A] in
theorem pull_eq_zero_of_factor {X : Scheme.{0}} {c : Pic X} {Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : pull f c = 0) : pull (g ≫ f) c = 0 := by
  rw [pull_comp, h, map_zero]

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem lam_eq_zero (hA : IsAbelianScheme A)
    (h₁ : pull (lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0)
    (h₂ : pull (lift (𝟙 A) (1 : A ⟶ A)).left (cls P hP) = 0) {T : Over S} (x : T ⟶ A)
    (hx : pull (lift (snd A T ≫ x) (fst A T)).left (cls P hP) = 0) :
    lam (cls P hP) (fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A)) (snd T (G2 A)) = 0 := by
  let W := T ⊗ G2 A
  let x' : W ⟶ A := fst T (G2 A) ≫ x
  let b₁ : W ⟶ A := snd T (G2 A) ≫ fst A A
  let b₂ : W ⟶ A := snd T (G2 A) ≫ snd A A
  have l₁ : ∀ b : W ⟶ A, DiagPairing.pc hP 1 b = 0 := fun b => by
    have e : (lift (1 : W ⟶ A) b) = b ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₁
  have l₂ : ∀ a : W ⟶ A, DiagPairing.pc hP a 1 = 0 := fun a => by
    have e : (lift a (1 : W ⟶ A)) = a ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₂
  have l₃ : DiagPairing.pc hP x' b₂ = 0 := by
    have e : (lift x' b₂) = lift b₂ (fst T (G2 A)) ≫ lift (snd A T ≫ x) (fst A T) := by
      rw [comp_lift, lift_snd_assoc, lift_fst]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ hx
  have one : (1 : W ⟶ G2 A) = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ea : fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A) = lift x' 1 := by
    rw [comp_lift, MonObj.comp_one]
  have eb : snd T (G2 A) = lift b₁ b₂ := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have e := cube_cls hA hP (lift x' 1) (lift b₁ 1) (lift 1 b₂)
  simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, one] at e
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP (x' * b₁) 1 - DiagPairing.pc hP x' b₂
    - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP x' 1 + DiagPairing.pc hP b₁ 1 + DiagPairing.pc hP 1 b₂
    - DiagPairing.pc hP 1 1 = 0 at e
  rw [l₁, l₁, l₂, l₂, l₂, l₃] at e
  rw [lam, ea, eb, one, lift_mul_lift, _root_.one_mul]
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP x' 1 - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP 1 1 = 0
  rw [l₁, l₂, ← e]
  abel

end GlobalTheory.KernelPointPairing
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hodgeLineBundle_eighthPower_iso_pow : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  first | exact @GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight | exact GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight | (intros; apply GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight <;> assumption)
end
