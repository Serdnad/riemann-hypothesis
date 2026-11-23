module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductDegenerationDataSum
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdIndep

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep GlobalTheory.BoxFamIndep

theorem tensor_indep (F O₁ O₂ : Type) [Field F] [CommRing O₁] [Algebra F O₁] [CommRing O₂] [Algebra F O₂]
    {A₁ A₂ : Type} {m n : ℕ} (β₁ : A₁ → Fin m → O₁) (β₂ : A₂ → Fin n → O₂)
    (h₁ : ∀ c : Fin m → F, (∀ α, ∑ l, c l • β₁ α l = 0) → c = 0)
    (h₂ : ∀ c : Fin n → F, (∀ α, ∑ l, c l • β₂ α l = 0) → c = 0) (c : Fin m × Fin n → F)
    (hc : ∀ α₁ α₂, ∑ a, c a • (β₁ α₁ a.1 ⊗ₜ[F] β₂ α₂ a.2) = 0) : c = 0 := by
  have key : ∀ α₁ α₂, ∑ l : Fin m, β₁ α₁ l ⊗ₜ[F] (∑ a : Fin n, c (l, a) • β₂ α₂ a) = 0 := by
    intro α₁ α₂
    rw [← hc α₁ α₂, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun a _ => TensorProduct.tmul_smul _ _ _
  have key2 : ∀ l, (fun a : Fin n => c (l, a)) = 0 := fun l => h₂ _ fun α => by
    refine (Module.forall_dual_apply_eq_zero_iff F _).1 fun φ => ?_
    refine congrFun (h₁ (fun l => φ (∑ a : Fin n, c (l, a) • β₂ α a)) fun α₀ => ?_) l
    have := congrArg (fun t => TensorProduct.rid F O₁ (LinearMap.lTensor O₁ φ t)) (key α₀ α)

    simpa only [map_sum (LinearMap.lTensor O₁ φ), map_sum (TensorProduct.rid F O₁), LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, map_zero] using this
  funext a
  exact congrFun (key2 a.1) a.2

theorem exists_test₂ {F : Type} [Field F] {X₁ X₂ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of F))
    (p₂ : X₂ ⟶ Spec (CommRingCat.of F)) (x₁ : X₁) (x₂ : X₂) {A₁ A₂ : Type} {U₁ : A₁ → X₁.Opens}
    {U₂ : A₂ → X₂.Opens} (hx₁ : ∀ α, x₁ ∈ U₁ α) (hx₂ : ∀ α, x₂ ∈ U₂ α) {m n : ℕ}
    (s₁ : ∀ α, Fin m → Γ(X₁, U₁ α)) (s₂ : ∀ α, Fin n → Γ(X₂, U₂ α))
    (hs₁ : ∀ c : Fin m → F, (∀ α, ∑ l, germOf p₁ x₁ (c l) * gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l) = 0) → c = 0)
    (hs₂ : ∀ c : Fin n → F, (∀ α, ∑ l, germOf p₂ x₂ (c l) * gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l) = 0) → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂), r₁ ≫ p₁ = q ∧ r₂ ≫ p₂ = q ∧
      (∀ z α, r₁ z ∈ U₁ α) ∧ (∀ z α, r₂ z ∈ U₂ α) ∧ ∀ c : Fin m × Fin n → F,
        (∀ α₁ α₂ z, ∑ a, germOf q z (c a) * (gs r₁ z (U₁ α₁) (s₁ α₁ a.1) * gs r₂ z (U₂ α₂) (s₂ α₂ a.2)) = 0) →
          c = 0 := by
  let : Algebra F (X₁.presheaf.stalk x₁) := (germOf p₁ x₁).toAlgebra
  let : Algebra F (X₂.presheaf.stalk x₂) := (germOf p₂ x₂).toAlgebra
  have h := tensor_indep F _ _ (fun α l => gs (𝟙 X₁) x₁ (U₁ α) (s₁ α l)) (fun α l => gs (𝟙 X₂) x₂ (U₂ α) (s₂ α l))
    (fun c hc => hs₁ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
    (fun c hc => hs₂ c fun α => by
      have := hc α
      simp only [Algebra.smul_def] at this
      exact this)
  obtain ⟨B, _, _, e₁, e₂, h⟩ : ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (e₁ : X₁.presheaf.stalk x₁ →ₐ[F] B)
      (e₂ : X₂.presheaf.stalk x₂ →ₐ[F] B), ∀ c : Fin m × Fin n → F, (∀ α₁ α₂, ∑ a, c a •
        (e₁ (gs (𝟙 X₁) x₁ (U₁ α₁) (s₁ α₁ a.1)) * e₂ (gs (𝟙 X₂) x₂ (U₂ α₂) (s₂ α₂ a.2))) = 0) → c = 0 :=
    ⟨TensorProduct F (X₁.presheaf.stalk x₁) (X₂.presheaf.stalk x₂), inferInstance, inferInstance,
      Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, fun c hc => h c fun α₁ α₂ => by
        rw [← hc α₁ α₂]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]⟩
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    (Spec.map (CommRingCat.ofHom e₁.toRingHom) : _ ⟶ Spec (X₁.presheaf.stalk x₁)) ≫ X₁.fromSpecStalk x₁,
    (Spec.map (CommRingCat.ofHom e₂.toRingHom) : _ ⟶ Spec (X₂.presheaf.stalk x₂)) ≫ X₂.fromSpecStalk x₂,
    ?_, ?_, fun z α => fromSpecStalk_mem x₁ (hx₁ α) _, fun z α => fromSpecStalk_mem x₂ (hx₂ α) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₁.commutes a
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact e₂.commutes a
  · refine h c fun α₁ α₂ => eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_

    rw [← hc α₁ α₂ z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_)
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · rw [gs_fromSpecStalk x₁ (hx₁ _)]
      exact (germOf_map (B := X₁.presheaf.stalk x₁) (𝟙 _) (CommRingCat.ofHom e₁.toRingHom) z _).symm
    · rw [gs_fromSpecStalk x₂ (hx₂ _)]
      exact (germOf_map (B := X₂.presheaf.stalk x₂) (𝟙 _) (CommRingCat.ofHom e₂.toRingHom) z _).symm

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem exists_pt {D : DegPre R} {m : ℕ} (b : Fin m → Fam D F k) (hb : LinearIndependent F b) :
    ∃ (x : (DegPre.BF D F).left) (jj : D.X → Fin 4 → D.P.L.ι),
      (∀ α, x ∈ LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) ∧ ∀ c : Fin m → F,
      (∀ α, ∑ l, germOf (B := CommRingCat.of F) (fst (TF (R := R) F) D.P.A).left x (c l) *
        gs (𝟙 _) x (LB.wchart D.P.L (DegPre.famφ D F α) (jj α)) (((b l).s α).f (jj α)) = 0) → c = 0 := by
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (DegPre.BF D F).left :=
    hg.geometrically_isIntegral (TF (R := R) F).hom _ _ (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
  choose J₀ hJ₀ using fun χ : (DegPre.BF D F).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (DegPre.BF D F).left))
  have hx : ∀ α, genericPoint (DegPre.BF D F).left ∈
      LB.wchart D.P.L (DegPre.famφ D F α) (fun a => J₀ (DegPre.famφ D F α a)) :=
    fun α => Set.mem_iInter.2 fun a => hJ₀ _
  refine ⟨_, _, hx, fun c hc => funext <| Fintype.linearIndependent_iff.1 hb c <| fam_ext fun α jj => ?_⟩
  refine fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint (DegPre.BF D F).left ∈ LB.wchart D.P.L (DegPre.famφ D F α) jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  refine (sec_trans _ (𝟙 _) _ hy' (hx α)).trans ?_
  refine (congrArg _ ((gs_comb c b α _ (𝟙 _) _ (hx α)).trans ?_)).trans (mul_zero _)
  rw [Category.id_comp]
  exact hc α

theorem exists_pair {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) [IsIso (lift p₁ p₂)]
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of F)) (r₁ : Z ⟶ (DegPre.BF D₁ F).left)
    (r₂ : Z ⟶ (DegPre.BF D₂ F).left) (h₁ : r₁ ≫ (fst (TF (R := R) F) D₁.P.A).left = q)
    (h₂ : r₂ ≫ (fst (TF (R := R) F) D₂.P.A).left = q) :
    ∃ ρ : Z ⟶ (DegPre.BF D F).left, ρ ≫ (TF (R := R) F ◁ p₁).left = r₁ ∧ ρ ≫ (TF (R := R) F ◁ p₂).left = r₂ ∧
      ρ ≫ (fst (TF (R := R) F) D.P.A).left = q := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (q ≫ (TF (R := R) F).hom)
  let q' : T ⟶ TF (R := R) F := Over.homMk q rfl
  let r₁' : T ⟶ DegPre.BF D₁ F := Over.homMk r₁ (by
    rw [← Over.w (fst (TF (R := R) F) D₁.P.A), ← Category.assoc, h₁]; rfl)
  let r₂' : T ⟶ DegPre.BF D₂ F := Over.homMk r₂ (by
    rw [← Over.w (fst (TF (R := R) F) D₂.P.A), ← Category.assoc, h₂]; rfl)
  let ρ : T ⟶ DegPre.BF D F := lift q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _))
  have hρ₁ : ρ ≫ TF (R := R) F ◁ p₁ = r₁' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₁.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_fst _ _ _ _
  have hρ₂ : ρ ≫ TF (R := R) F ◁ p₂ = r₂' := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, lift_fst]
      exact Over.OverMorphism.ext h₂.symm
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, lift_snd]
      exact SumDeg.pairPt_snd _ _ _ _
  exact ⟨ρ.left, congrArg (fun g => g.left) hρ₁, congrArg (fun g => g.left) hρ₂,
    congrArg (fun g => g.left) (lift_fst q' (SumDeg.pairPt p₁ p₂ (r₁' ≫ snd _ _) (r₂' ≫ snd _ _)))⟩

theorem boxFam₂_linearIndependent : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w F _ _ k m n b₁ b₂ b hb₁ hb₂ hb
  refine Fintype.linearIndependent_iff.2 fun c hc => congrFun (?_ : c = 0)
  have := hS.lim
  obtain ⟨x₁, j₁, hx₁, H₁⟩ := exists_pt b₁ hb₁
  obtain ⟨x₂, j₂, hx₂, H₂⟩ := exists_pt b₂ hb₂
  obtain ⟨Z, q, r₁, r₂, hq₁, hq₂, hr₁, hr₂, H⟩ := exists_test₂ (F := F) (fst (TF (R := R) F) D₁.P.A).left
    (fst (TF (R := R) F) D₂.P.A).left x₁ x₂ hx₁ hx₂ (fun α l => ((b₁ l).s α).f (j₁ α))
    (fun α l => ((b₂ l).s α).f (j₂ α)) H₁ H₂
  obtain ⟨ρ, hρ₁, hρ₂, hρq⟩ := exists_pair p₁ p₂ q r₁ r₂ hq₁ hq₂
  refine H c fun α₁ α₂ z => ?_
  obtain ⟨α, rfl, rfl⟩ : ∃ α, q₁ α = α₁ ∧ q₂ α = α₂ := by
    obtain ⟨α, h⟩ := hS.xsum.2 (α₁, α₂)
    exact ⟨α, congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB z
  have hm := hJ.mem (DegPre.famφ D F α) ρ
  have E := (gs_comb c b α _ ρ z hm).symm.trans
    ((congrArg (fun s : Fam D F k => gs (Y := Z) ρ z _ ((s.s α).f _)) hc).trans (gs_zero _ _ _ hm))
  rw [hρq] at E
  have E' := fun a => hb a α Z ρ z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [hρ₁, hρ₂] at E'
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a, u * sval (Z := Z) ((b a).s α) ρ z J =
      sval ((b₁ a.1).s (q₁ α)) r₁ z J₁ * sval ((b₂ a.2).s (q₂ α)) r₂ z J₂ := ⟨_, E'⟩
  obtain ⟨v₁, hv₁⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₁ z (LB.wchart D₁.P.L (DegPre.famφ D₁ F (q₁ α)) (j₁ (q₁ α))) (((b₁ l).s (q₁ α)).f (j₁ (q₁ α))) =
      v * sval ((b₁ l).s (q₁ α)) r₁ z J₁ :=
    ⟨_, fun l => sec_trans _ r₁ z (hr₁ z _) (hJ₁.mem _ r₁)⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : Z.presheaf.stalk z, ∀ l,
      gs r₂ z (LB.wchart D₂.P.L (DegPre.famφ D₂ F (q₂ α)) (j₂ (q₂ α))) (((b₂ l).s (q₂ α)).f (j₂ (q₂ α))) =
      v * sval ((b₂ l).s (q₂ α)) r₂ z J₂ :=
    ⟨_, fun l => sec_trans _ r₂ z (hr₂ z _) (hJ₂.mem _ r₂)⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((v₁ * v₂) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((congrArg₂ (· * ·) (hv₁ a.1) (hv₂ a.2)).trans (_root_.mul_mul_mul_comm _ _ _ _)).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

end GlobalTheory.ProdIndep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
namespace GlobalTheory.ProdUnif

open GlobalTheory.WCub GlobalTheory.PowUnif



theorem cubAlong_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ hS wM L c wL hLB hM hL e g h₁ h₂ w hQ T x jL jM cL cM
  have := g.q_hom
  have := (U₁.gt e).q_hom
  have := (U₂.gt e).q_hom
  have := hS.hom₁
  have := hS.hom₂
  refine (clause_iff (tri (thick R I e) g.pG x) (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x)
    (fun k : thK => (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (c.s jL)
    (fun k => w.s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hG' _ => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 hB k)
  obtain ⟨N, hN, eN⟩ := exists_good L hLB y _ jL cL (fun k => Set.mem_iInter.1 hG' k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.toPre.P.isLB y
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at U₁.LG.isLB y
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at U₂.LG.isLB y
  have tM₁ := (tri_map (thick R I e) (U₁.gt e).pG g.pG x _ p₁ h₁).2
  have tM₂ := (tri_map (thick R I e) (U₂.gt e).pG g.pG x _ p₂ h₂).2
  have tL₁ := (tri_map (thick R I e) (fstG I e G₁) (fstG I e (G₁ ⊗ G₂)) x _ (fst G₁ G₂)
    (thick_fstG I e (fst G₁ G₂))).2
  have tL₂ := (tri_map (thick R I e) (fstG I e G₂) (fstG I e (G₁ ⊗ G₂)) x _ (snd G₁ G₂)
    (thick_fstG I e (snd G₁ G₂))).2
  have bM := hM T.left (tri (thick R I e) g.pG x) y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [tM₁, tM₂] at bM
  have bL := hL T.left (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x) y N₁ N₂ N hN₁ hN₂ hN
  rw [tL₁, tL₂] at bL
  have v₁ := w_cub_val.{0} U₁ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) y hJ₁ hN₁
  have v₂ := w_cub_val.{0} U₂ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) y hJ₂ hN₂

  have fM := fun k : thK => tri_thφ (thick R I e) g.pG x g.q rfl k
  have fG := fun k : thK => tri_thφ (thick R I e) (fstG I e (G₁ ⊗ G₂)) x (𝟙 _) (Category.id_comp _).symm k
  have fM₁ := fun k : thK => tri_thφ (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (U₁.gt e).q rfl k
  have fM₂ := fun k : thK => tri_thφ (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (U₂.gt e).q rfl k
  have fG₁ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have fG₂ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have ps₁ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down
  have ps₂ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down
  have key := rel_alg thε
    (fun k => om wM y J₁ J₂ J (tri (thick R I e) g.pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
    (fun k => om wL y N₁ N₂ N (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x ≫ thφ (G₁ ⊗ G₂) (x3 (G₁ ⊗ G₂)) k))
    (fun k => gw w (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y (jM k) (fun _ => jL k))
    (fun k => gw (U₁.w e) (psum (thickObj R I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down).left y
      (J₁ (tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k))
      (fun _ => N₁ (tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k)))
    (fun k => gw (U₂.w e) (psum (thickObj R I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down).left y
      (J₂ (tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k))
      (fun _ => N₂ (tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k)))
    (fun k => by
      have q := hQ T.left (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      have a₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₁.left =
          tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k := by
        rw [Category.assoc, h₁, ← Category.assoc, ps₁ k, fM₁ k]
      have a₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₂.left =
          tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k := by
        rw [Category.assoc, h₂, ← Category.assoc, ps₂ k, fM₂ k]
      have b₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (fst G₁ G₂).left =
          tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k := by
        rw [Category.assoc, thick_fstG I e (fst G₁ G₂), ← Category.assoc, ps₁ k, fG₁ k]
      have b₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (snd G₁ G₂).left =
          tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k := by
        rw [Category.assoc, thick_fstG I e (snd G₁ G₂), ← Category.assoc, ps₂ k, fG₂ k]
      rw [a₁, a₂, b₁, b₂, ps₁ k, ps₂ k, ← fM k, ← fG k, eJ k, eN k] at q
      exact q)
    bM bL v₁ v₂
  refine (val_of _ _ y J jM eJ).symm.trans (key.trans ?_)
  exact congrArg _ (val_of c _ y N jL eN)

end GlobalTheory.ProdUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UCanon

theorem torsion_sec_over_second : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  intro k _ S G' _ hab G _ g₁ g₂ φ₁ φ₂ h₂ h0 hg n hn σ hσ x hx hx₁
  let T := 𝟙_ (Over (Sp (DualNumber k)))
  have hsq : ∀ y : T ⟶ G', (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g₂ := by
    intro y
    rw [Category.assoc, h₂.1.w, ← Category.assoc, Over.w y]
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ g₂) ⟶ G) := fun y => Over.homMk (y.left ≫ φ₂) (hsq y)
  have ψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    apply Over.OverMorphism.ext
    exact (h₂.2 T a b (ψ a) (ψ b) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ g₂) ⟶ G) := MonoidHom.mk' ψ ψmul
  have Ψinj : ∀ a b : T ⟶ G', Ψ a = Ψ b → a = b := by
    intro a b hab'
    apply Over.OverMorphism.ext
    exact h₂.1.hom_ext (congrArg CommaMorphism.left hab') (by rw [Over.w a, Over.w b])
  have hw : (g₂ ≫ σ.left) ≫ G.hom = 𝟙 (Sp (DualNumber k)) ≫ g₂ := by
    rw [Category.assoc, Over.w σ]; simp
  let x' : T ⟶ G' := Over.homMk (h₂.1.lift (g₂ ≫ σ.left) (𝟙 _) hw) (by simp [T])
  have hx'φ : x'.left ≫ φ₂ = g₂ ≫ σ.left := h₂.1.lift_fst _ _ _
  let u : Over.mk (T.hom ≫ g₂) ⟶ 𝟙_ (Over S) := toUnit _
  have hu : u.left = g₂ := by
    have := Over.w u
    simpa [T] using this
  have hΨx' : Ψ x' = u ≫ σ := by
    apply Over.OverMorphism.ext
    show x'.left ≫ φ₂ = u.left ≫ σ.left
    rw [hx'φ, hu]
  have hpow : ∀ m : ℕ, u ≫ σ ^ m = (u ≫ σ) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have hx'n : x' ^ n = 1 := by
    apply Ψinj
    rw [map_pow, map_one, hΨx', ← hpow, hσ, MonObj.comp_one]
  have hb : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left := by
    apply h₂.1.hom_ext
    · have h1 := h0 (Sp k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left) (𝟙 _)
        (by rw [Category.assoc, Over.w x]; simp [T])
      rw [← h1, Category.assoc, Category.assoc, hx₁, ← Category.assoc, hg, Category.assoc, hx'φ]
    · rw [Category.assoc, Category.assoc, Over.w x, Over.w x']
  have key := GlobalTheory.T.eq_of_nsmul_eq_of_eq_closedPoint_dualNumbers k G' hab n hn x x' (by rw [hx, hx'n]) hb
  rw [key]
  exact hx'φ

end GlobalTheory.UCanon
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem descend_glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  intro R _ _ _ _ S Y Z W π y p q hπp hπs hSi hy hpb O h I V hV h₀ hh
  have hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O := by
    rw [Scheme.Hom.preimage_iSup]; exact iSup_le hV
  haveI := hy
  have hflat : Flat ((⨆ i, V i).ι ≫ y) := inferInstance
  have hsq : IsPullback (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) ((⨆ i, V i).ι ≫ y) π :=
    (isPullback_morphismRestrict p (⨆ i, V i)).paste_vert hpb
  have loc : ∀ (i : I) (T : Scheme.{0}) (k : T ⟶ (p ⁻¹ᵁ (⨆ i, V i)).toScheme) (t : T ⟶ (V i).toScheme),
      k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι ≫ p = t ≫ (V i).ι → k ≫ Z.homOfLE hV' ≫ h = t ≫ h₀ i := by
    intro i T k t hkt
    have sq := isPullback_morphismRestrict p (V i)
    have w : t ≫ (V i).ι = (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) ≫ p := by rw [Category.assoc]; exact hkt.symm
    have h1 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ∣_ V i) = t := sq.lift_fst _ _ _
    have h2 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ⁻¹ᵁ V i).ι = k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι :=
      sq.lift_snd _ _ _
    have h3 : k ≫ Z.homOfLE hV' = sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ Z.homOfLE (hV i) := by
      rw [← cancel_mono O.ι]; simp [h2]
    rw [reassoc_of% h3, ← hh i, reassoc_of% h1]
  have heq : pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) =
      pullback.snd (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) := by
    let a : pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ⟶ Y :=
      pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι
    have hcov : TopologicalSpace.IsOpenCover (fun i => a ⁻¹ᵁ V i) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, eq_top_iff]
      intro x _
      have hx : a.base x ∈ Set.range (⨆ i, V i).ι.base := by
        have ha : a = (pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i))) ≫ (⨆ i, V i).ι :=
          (Category.assoc _ _ _).symm
        rw [ha]
        first
          | exact ⟨_, rfl⟩
          | (rw [Scheme.comp_base]; exact ⟨_, rfl⟩)
          | exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.Opens.range_ι] at hx
      exact hx
    refine Scheme.Cover.hom_ext ((pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i))).openCoverOfIsOpenCover _ hcov)
      _ _ fun i => ?_
    change (a ⁻¹ᵁ V i).ι ≫ _ = (a ⁻¹ᵁ V i).ι ≫ _
    rw [← Category.assoc, loc i _ _ (a ∣_ V i), ← Category.assoc, loc i _ _ (a ∣_ V i)]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι]
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq (Z.homOfLE hV' ≫ h) heq
  refine ⟨hV', m, hm, fun W' g g' hg => ?_⟩
  have key := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W' π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq ((p ∣_ (⨆ i, V i)) ≫ g)
    (by rw [pullback.condition_assoc])
  exact key.unique rfl hg.symm

end GlobalTheory.MorDescent
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.descent_transition_diagonal_inclusion_over_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, τ i i = (V i i).ι) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  first | exact @GlobalTheory.Mum.descend_transition_diag_over | exact GlobalTheory.Mum.descend_transition_diag_over | (intros; apply GlobalTheory.Mum.descend_transition_diag_over <;> assumption)
end
