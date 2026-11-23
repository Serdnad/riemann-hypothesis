module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle633
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep

@[expose] public section

section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem GlobalTheory.ThetaMove.ptSec_transl' {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (p x : T ⟶ A) :
    (ptSecT A p).left ≫ (translT A x).left = (ptSecT A (x * p)).left := by
  rw [← Over.comp_left]
  congr 1
  rw [ptSecT, translT, comp_lift, lift_fst, ptSecT, translPt_eq, MonObj.comp_mul, lift_fst_assoc, Category.id_comp,
    lift_snd]

theorem GlobalTheory.ThetaMove.translT_inv {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) :
    (translT A x).left ≫ (translT A x⁻¹).left = 𝟙 _ ∧ (translT A x⁻¹).left ≫ (translT A x).left = 𝟙 _ := by
  constructor
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, inv_mul_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]

theorem GlobalTheory.ThetaMove.transport_symLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ hφ f hf hf1 hf2 w₀ hw₀ x' x hx hx'
  have hPL := C.P.L.isLB
  have hAL := C.A.isLB
  have hGL := T.U.LG.isLB
  have hTL := T.A.isLB
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨w, hw, hgw⟩ := GlobalTheory.T.exists_lineBundleIso_restrict_along_section hGL hTL hgi w₀ hw₀
  have h₁ : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
      (snd (TFK (R := W) F) T.A.A).left ≫ (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β := by
    rw [Category.assoc]; exact hf2
  have hT1 := GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 x' x hx
  have hneg := GlobalTheory.T.traitFibreIso_comm_neg C T F f hf1 hf2
  have hinv : f ≫ (translT C.A.A x⁻¹).left = (translT T.A.A x'⁻¹).left ≫ f := by
    calc f ≫ (translT C.A.A x⁻¹).left
        = ((translT T.A.A x'⁻¹).left ≫ (translT T.A.A x').left) ≫ f ≫ (translT C.A.A x⁻¹).left := by
          rw [(translT_inv x').2, Category.id_comp]
      _ = (translT T.A.A x'⁻¹).left ≫ (f ≫ (translT C.A.A x).left) ≫ (translT C.A.A x⁻¹).left := by
          rw [hT1]; simp only [Category.assoc]
      _ = (translT T.A.A x'⁻¹).left ≫ f := by
          rw [Category.assoc, (translT_inv x).1, Category.comp_id]
  have hpt : ∀ i : ℕ, (ptSecT T.A.A (x' ^ i)).left ≫ f = (ptSecT C.A.A (x ^ i)).left := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, pow_zero, ← inv_mul_cancel x', ← inv_mul_cancel x, ← ptSec_transl', ← ptSec_transl',
        Category.assoc, ← hinv, ← Category.assoc, hx]
    | succ i ih =>
      rw [pow_succ', pow_succ', ← ptSec_transl', ← ptSec_transl', Category.assoc, ← hT1, ← Category.assoc, ih]
  have hpow : ∀ i : ℕ, f ≫ (translT C.A.A (x ^ i)).left = (translT T.A.A (x' ^ i)).left ≫ f :=
    fun i => GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 _ _ (hpt i)
  have hG0 : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.G.hom =
      (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    have e1 : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have e2 : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom = (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have e3 : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
      unfold jFK jK spMap
      rw [← Spec.map_comp]
      rfl
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.U.gen.inv.left, e1, ← Category.assoc,
      e2, Category.assoc, e3]
  let JPc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ C.G.left) → C.P.L.L.ι := fun z ψ => (exists_chart hPL (ψ z)).choose
  have gJP : ∀ {Z : Scheme.{0}} (z : Z), Good C.P.L.L z (JPc z) := fun z ψ => (exists_chart hPL (ψ z)).choose_spec
  let JGc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ T.G.left) → T.U.LG.L.ι := fun z ψ => (exists_chart hGL (ψ z)).choose
  have gJG : ∀ {Z : Scheme.{0}} (z : Z), Good T.U.LG.L z (JGc z) := fun z ψ => (exists_chart hGL (ψ z)).choose_spec
  let Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) → ∀ z : Z, ((Z ⟶ C.A.A.left) → C.A.L.ι) →
      ((Z ⟶ T.A.A.left) → T.A.L.ι) → (Z.presheaf.stalk z)ˣ := fun q z JA Jt =>
    tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left q z (JPc z) JA (JGc z) Jt
  have conv : ∀ (σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j))
      (τ : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) →
      ∀ (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) (z : Z) JA Jt, Good C.A.L z JA → Good T.A.L z Jt →
        sval τ (q ≫ f) z JA = (Ψ q z JA Jt ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt := by
    intro σ τ hr Z q z JA Jt hJA hJt
    have e := hr Z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) (q ≫ f) q
      rfl (by simp only [Category.assoc]; rw [hf2]) (by rw [Category.assoc, hG0]) z (JPc z) JA (JGc z) Jt (gJP z) hJA
      (gJG z) hJt
    simp only [Category.assoc] at e
    show sval τ (q ≫ f) z JA = ((tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left
      q z (JPc z) JA (JGc z) Jt) ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt
    simp only [tf, hgw, Category.assoc]
    rw [zpow_natCast, mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul]
    calc sval τ (q ≫ f) z JA
        = (((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left))) ^ (C.n ^ j))⁻¹).val *
          ((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ (q ≫ f) z JA) := by
          rw [← _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
      _ = _ := by rw [e]; ring
  have hs₂ : ∀ p : TFK (R := W) F ⟶ T.A.A, (translT T.A.A p).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (translPt T.A.A p).left := fun p => by rw [← Over.comp_left, translT, lift_snd]
  have hn₂ : (negT T.A.A (TFK (R := W) F)).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left := by rw [← Over.comp_left, negT, lift_snd]
  have hn₃ : (negT T.A.A (TFK (R := W) F)).left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left =
      f ≫ (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left := by
    rw [← Category.assoc, ← hneg, Category.assoc, ← Over.comp_left, negT, lift_snd]
  have hs₃ : (translT T.A.A x').left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left = f ≫ (translPt C.A.A x).left := by
    rw [← Category.assoc, ← hT1, Category.assoc, ← Over.comp_left, translT, lift_snd]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨pt', φ', hφ'⟩, hs'⟩
    have e0 : pt' = x' := hs'.pt_eq
    subst e0
    obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A x).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A pt').left (translT T.A.A pt').left h₁
      (hs₂ pt') hs₃ ((C.n ^ j : ℕ) : ℤ) φ' hφ'
    obtain ⟨ν', hν', hsym'⟩ := hs'.sym
    obtain ⟨ν, hν, hvν⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν' hν'
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x, u, hu⟩, ⟨rfl, corr_of_val hAL fun y J hJ => ?_, ν, hν, corr_of_val hAL fun y J hJ => ?_⟩⟩
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ Ψ hpow hx' Hu _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hs'.pow_eq (inv f), val_one, val_one]
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ ν ν' Ψ hinv hneg Hu Hν _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hsym' (inv f), val_one, val_one]
  · rintro ⟨pt, φ, hφ⟩ hs
    have e0 : pt = x := hs.pt_eq
    subst e0
    obtain ⟨u', hu', hvu'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A pt).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A x').left (translT T.A.A x').left h₁
      (hs₂ x') hs₃ ((C.n ^ j : ℕ) : ℤ) φ hφ
    obtain ⟨ν, hν, hsym⟩ := hs.sym
    obtain ⟨ν', hν', hvν'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν hν
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x', u', hu'⟩, ⟨rfl, corr_of_val hTL fun y J' hJ' => ?_, ν', hν', corr_of_val hTL fun y J' hJ' => ?_⟩, ?_⟩
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hpow hx' Hu _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hs.pow_eq, val_one, val_one]
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ ν ν' Ψ hinv hneg Hu Hν _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hsym, val_one, val_one]
    · intro σ σ' τ τ' hr hr' hact
      exact GlobalTheory.T.thetaGroupAction_compat_fibreIso hAL hTL f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hT1 Hu σ σ' τ τ' (conv σ τ hr) (conv σ' τ' hr') hact
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitRescale

variable {X Z : Scheme.{0}}

noncomputable def gsTop (f : Z ⟶ X) (z : Z) : Γ(X, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (f ⁻¹ᵁ ⊤) z trivial).hom.comp (f.app ⊤).hom

theorem gs_top (f : Z ⟶ X) (z : Z) (a : Γ(X, ⊤)) : gs f z ⊤ a = gsTop f z a := gs_eq f z ⊤ trivial a

theorem scal_comp {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ spMap φ) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) (x y : A) :
    scal q (x * y) = scal q x * scal q y := by simp only [scal, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) : scal q 1 = 1 := by
  simp only [scal, map_one]

theorem gs_top_mul (f : Z ⟶ X) (z : Z) (a b : Γ(X, ⊤)) : gs f z ⊤ (a * b) = gs f z ⊤ a * gs f z ⊤ b :=
  gs_mul f z ⊤ trivial a b

theorem gs_top_one (f : Z ⟶ X) (z : Z) : gs f z ⊤ 1 = 1 := by rw [gs_top, map_one]

theorem gs_scal {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem gs_scal_compat {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  rw [scal_comp, scal_comp, gs_scal, gs_scal]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem sval_smul {Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [show (a • s).f (fun k => J (r ≫ φ k)) = resG Y le_top a * s.f (fun k => J (r ≫ φ k)) from
    GlobalTheory.LB.smul_f a s _]
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

end GlobalTheory.Mum.TraitRescale


open GlobalTheory.Mum.TraitRescale in
theorem GlobalTheory.Mum.Trait.exp_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b : W) (u : Wˣ) (c₁ c₂ : R), a ≠ 0 → c₂ ≠ 0 → T.φ c₂ * (u : W) * a = T.φ c₁ * b → T.Exp a b s F → T.Exp 1 u (scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • s) F := by
  intro R _ _ _ hB D C W _ _ _ T k s F a b u c₁ c₂ ha hc₂ hrel hExp
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hagree⟩ := hExp
  obtain ⟨σ'', hcar''⟩ := GlobalTheory.T.exists_carries_transport_uniformising_iso R D C W T k (u : W) σ'
  refine ⟨σ'', ⟨σ', f', hcar'', hpull, hexp⟩, ?_⟩
  have hφ2 : T.φ c₂ ≠ 0 := fun h0 => hc₂ (T.inj (h0.trans (map_zero T.φ).symm))
  have hb : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hrel
    exact (mul_ne_zero (mul_ne_zero hφ2 u.ne_zero) ha) hrel
  set c : FractionRing R := algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂ with hc
  have hc₂K : algebraMap R (FractionRing R) c₂ ≠ 0 :=
    fun h0 => hc₂ (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  have hcc : c * algebraMap R (FractionRing R) c₂ = algebraMap R (FractionRing R) c₁ := div_mul_cancel₀ _ hc₂K
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ'' p z J =
        gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J) := by
    intro Z p p' h z J hJ
    choose J' hJ' using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
    have e1 := hcar Z p z J J' hJ hJ'
    have e2 := hcar'' Z p z J J' hJ hJ'
    have e3 := hagree Z p p' h z J hJ

    have m : gs p z ⊤ (scal T.G.hom (T.φ c₂)) * gs p z ⊤ (scal T.G.hom (u : W)) * gs p z ⊤ (scal T.G.hom a) =
        gs p z ⊤ (scal T.G.hom (T.φ c₁)) * gs p z ⊤ (scal T.G.hom b) := by
      have := congrArg (fun w => gs p z ⊤ (scal T.G.hom w)) hrel
      simpa only [scal_mul, GlobalTheory.Mum.TraitRescale.gs_top_mul] using this
    rw [gs_scal_compat T p p' h z c₁, gs_scal_compat T p p' h z c₂] at m
    have hC : gs p' z ⊤ (scal C.A.A.hom c) * gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) =
        gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₁)) := by
      rw [← hcc, scal_mul, GlobalTheory.Mum.TraitRescale.gs_top_mul]
    have hU : IsUnit (gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) := by
      obtain ⟨v, hv⟩ := Ne.isUnit hc₂K
      have : IsUnit (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) :=
        IsUnit.of_mul_eq_one (scal C.A.A.hom ((v⁻¹ : (FractionRing R)ˣ) : FractionRing R))
          (by rw [← scal_mul, ← hv, Units.mul_inv, scal_one])
      rw [gs_top]
      exact this.map _
    have e13 := e1.symm.trans e3
    rw [e2]
    apply hU.mul_right_cancel
    linear_combination (gs p z ⊤ (scal T.G.hom (u : W)) *
      gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) * e13 + sval s p' z J * m -
      (gs p z ⊤ (scal T.G.hom b) * sval s p' z J) * hC
  intro Z p p' h z J hJ
  rw [scal_one, gs_top_one, _root_.one_mul, sval_smul C.P.L.L _ s p' z hJ]
  by_cases hF : IsField R
  · exact GlobalTheory.T.trait_scalar_cancel_of_isField R hB D C W T k σ'' s b c hF hb key Z p p' h z J hJ
  · exact (GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield R D C W T Z p p' h hF b hb z).mul_left_cancel (key Z p p' h z J hJ)

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThFam

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem gs_scal_one {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (y : Y) : gs (𝟙 Y) y ⊤ (scal p 1) = 1 := by
  have h : scal p (1 : R) = 1 := by simp [scal]
  rw [h, gs_eq _ y ⊤ trivial, map_one, map_one]

theorem secScal_generic (D : DegData R (maximalIdeal R)) (k : ℕ) (α : D.toPre.X) (b : D.toPre.SecB k α) :
    GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k)
      (GlobalTheory.FieldBaseChange.genericTerm D k α b) (D.toPre.famφB α) (DegPre.famε k) b
      (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
  refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  exact (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).symm.trans
    ((_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_one _ y).symm))

theorem lead_units {X : Type} [AddCommGroup X] (κ κ' : X → (FractionRing R)ˣ) (u : X → Rˣ)
    (hu : ∀ a, ((κ' a : (FractionRing R)ˣ) : FractionRing R) = (κ a : FractionRing R) * algebraMap R (FractionRing R) (u a : R))
    (k : ℕ) (α mu : X) :
    ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) = (lead κ' k α mu : FractionRing R) *
      algebraMap R (FractionRing R) (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R) := by
  have e : ∀ x : Rˣ, algebraMap R (FractionRing R) ((x⁻¹ : Rˣ) : R) = (algebraMap R (FractionRing R) (x : R))⁻¹ :=
    fun x => map_units_inv (algebraMap R (FractionRing R) : R →* FractionRing R) x
  have ne : ∀ x : Rˣ, algebraMap R (FractionRing R) (x : R) ≠ 0 := fun x =>
    (x.isUnit.map (algebraMap R (FractionRing R))).ne_zero
  have h₁ := ne (u mu); have h₂ := ne (u (mu + α)); have h₃ := ne (u α)
  have h₄ := (κ mu).ne_zero; have h₅ := (κ (mu + α)).ne_zero; have h₆ := (κ α).ne_zero
  simp only [lead, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu, e, map_mul, map_pow]
  field_simp
  ring

theorem core (hR : Base R) (D : DegData R (maximalIdeal R)) (κ : D.toPre.X → (FractionRing R)ˣ)
    (hκ : Reads D.toPre κ) (κ' : D.toPre.X → (FractionRing R)ˣ)
    (hu : ∀ a, ∃ u : Rˣ, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      (κ a : FractionRing R) * algebraMap R (FractionRing R) (u : R))
    (k : ℕ) (hk : 1 ≤ k) (α : D.toPre.X)
    (h1 : ∀ mu, mu ≠ 0 → ∃ s ∈ maximalIdeal R,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s)
    (h2 : ∀ n : ℕ, {mu | ¬ ∃ s ∈ maximalIdeal R ^ n,
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s}.Finite)
    (b : D.toPre.SecB k α) : ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b := by
  classical
  choose u hu using hu
  have inj := IsFractionRing.injective R (FractionRing R)
  have h1' : ∀ mu, ∃ s : R, mu ≠ 0 → s ∈ maximalIdeal R ∧
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s := fun mu => by
    by_cases h : mu = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨s, hs, e⟩ := h1 mu h
      exact ⟨s, fun _ => ⟨hs, e⟩⟩
  choose s hs using h1'
  let w : D.toPre.X → R := fun mu => (((u mu ^ k * (u (mu + α) * (u mu)⁻¹ * (u α)⁻¹))⁻¹ : Rˣ) : R)
  let r : D.toPre.X → R := fun mu => s mu * w mu
  have hr : ∀ mu, mu ≠ 0 → algebraMap R (FractionRing R) (r mu) =
      ((lead κ k α mu : (FractionRing R)ˣ) : FractionRing R) ∧ r mu ∈ maximalIdeal R := fun mu h =>
    ⟨by rw [lead_units κ κ' u hu k α mu, (hs mu h).2, map_mul], Ideal.mul_mem_right _ _ (hs mu h).1⟩
  have key : ∀ mu, mu ≠ 0 → ∀ e : ℕ, r mu ∉ maximalIdeal R ^ (e + 1) → ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
      ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s' := by
    rintro mu h e hn ⟨s', hs'm, hs'e⟩
    have : s mu = s' := inj ((hs mu h).2.symm.trans hs'e)
    exact hn (Ideal.mul_mem_right _ _ (this ▸ hs'm))
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hcls : ∀ a c : D.toPre.X, α + k • a = α + k • c → a = c := fun a c h => by
    have h' : (k : ℤ) • a = (k : ℤ) • c := by simpa using add_left_cancel h
    exact smul_right_injective D.toPre.X (show (k : ℤ) ≠ 0 by omega) h'
  obtain ⟨F, hFα, hF0⟩ := ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep (F := FractionRing R) hG D.tau_bimult k α hcls
    (GlobalTheory.FieldBaseChange.genericTerm D k α b)
  have hb : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
      (D.toPre.famφB α) (DegPre.famε k) b (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) := by
    rw [hFα]; exact secScal_generic D k α b
  have hex : ∀ β : D.toPre.X, ∃ g : D.toPre.SecB k β, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) β)
      (DegPre.famε k) (F.s β) (D.toPre.famφB β) (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing R)).left
      (scal (DegPre.BF D.toPre (FractionRing R)).hom 1) ∧ (β ≠ α → VanMod (maximalIdeal R) g 0 ∧
        ∀ e : ℕ, ¬ VanMod (maximalIdeal R) g e → ∃ mu, α + k • mu = β ∧ ¬ ∃ s' ∈ maximalIdeal R ^ (e + 1),
          ((lead κ' k α mu : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) s') := by
    intro β
    by_cases hβ : β = α
    · subst hβ
      exact ⟨b, hb, fun h => absurd rfl h⟩
    by_cases hc : ∃ mu, α + k • mu = β
    · obtain ⟨mu, rfl⟩ := hc
      have hmu : mu ≠ 0 := by
        rintro rfl
        exact hβ (by simp)
      obtain ⟨f, hf1, hf2⟩ := GlobalTheory.T.thetaFamily_translatedMembers_leading_times_integral R hR D κ hκ k hk α b F hb mu (r mu) (hr mu hmu).1
      refine ⟨f, hf1, fun _ => ⟨hf2 0 (by simpa using (hr mu hmu).2), fun e he => ⟨mu, rfl, ?_⟩⟩⟩
      exact key mu hmu e (fun h => he (hf2 e h))
    · push_neg at hc
      refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero, ?_, fun _ => ⟨fun j => map_zero _, fun e he => absurd (fun j => map_zero _) he⟩⟩
      refine (GlobalTheory.FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _),
        ReciprocityTheory.ChartRestriction.G.DVR.UUA.sval_zero_of (hF0 β hc) _ y J (hJ.mem _ _), mul_zero]
  choose g hg using hex
  refine ⟨⟨F, Function.update g α b, fun β => ?_, fun e => ?_⟩, Function.update_self α b g, fun β hβ => ?_⟩
  · by_cases h : β = α
    · subst h
      rw [Function.update_self]
      exact hb
    · rw [Function.update_of_ne h]
      exact (hg β).1
  · refine (((h2 (e + 1)).image (fun mu => α + k • mu)).insert α).subset fun β hβ => ?_
    by_cases h : β = α
    · exact Or.inl h
    · right
      have hβ' : ¬ VanMod (maximalIdeal R) (g β) e := by
        have := hβ
        simp only [Set.mem_setOf_eq] at this
        rwa [Function.update_of_ne h] at this
      obtain ⟨mu, hmu, hn⟩ := ((hg β).2 h).2 e hβ'
      exact ⟨mu, hn, hmu⟩
  · show VanMod (maximalIdeal R) (Function.update g α b β) 0
    rw [Function.update_of_ne hβ]
    exact ((hg β).2 hβ).1

theorem exists_intFam_lead : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), (∀ α : D.toPre.X, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ b : D.toPre.SecB k α,
      ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead α b) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ b : D.toPre.SecB k 0, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead 0 b := by
  intro R _ _ _ hR D
  haveI := hR.1.1
  haveI := hR.1.2.2.1
  obtain ⟨κ, hκ, hev, hcub, hpos, htend⟩ := GlobalTheory.T.exists_even_cubic_integral_reading_of_trivialisations R hR D
  obtain ⟨κ', hev', hcub', hu⟩ := GlobalTheory.T.exists_even_cubic_unit_multiple_fractionRing R D.toPre.X κ hev hcub
  have hu0 := hu
  choose u hu' using hu0
  have hpos' : ∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, ((κ' a : (FractionRing R)ˣ) : FractionRing R) =
      algebraMap R (FractionRing R) s := fun a ha => by
    obtain ⟨s, hs, e⟩ := hpos a ha
    exact ⟨s * u a, Ideal.mul_mem_right _ _ hs, by rw [hu' a, e, map_mul]⟩
  have h0 : κ' 0 = 1 := by
    have := hcub' 0 0 0
    simp only [add_zero] at this
    exact mul_eq_left.1 this
  refine ⟨fun α => ?_, fun k hk b => ?_⟩
  · obtain ⟨k₁, H⟩ := GlobalTheory.T.cubical_even_character_leading_terms_mem_maximalIdeal R D.toPre.X κ' hev' hcub' hpos' α
    exact ⟨max k₁ 1, fun k hk b => core hR D κ hκ κ' hu k (le_of_max_le_right hk) α
      (H k (le_of_max_le_left hk)).1 (H k (le_of_max_le_left hk)).2 b⟩
  · have hl : ∀ mu, lead κ' k 0 mu = κ' mu ^ k := fun mu => by
      simp [lead, h0]
    refine core hR D κ hκ κ' hu k hk 0 (fun mu hmu => ?_) (fun n => ?_) b
    · obtain ⟨s, hs, e⟩ := hpos' mu hmu
      exact ⟨s ^ k, Ideal.pow_mem_of_mem _ hs k (by omega), by rw [hl, Units.val_pow_eq_pow_val, e, map_pow]⟩
    · refine (htend n).subset fun mu hmu h => hmu ?_
      obtain ⟨s, hs, e⟩ := h
      refine ⟨(s * u mu) ^ k, Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ hs) k (by omega), ?_⟩
      rw [hl, Units.val_pow_eq_pow_val, hu' mu, e, ← map_mul, ← map_pow]

end GlobalTheory.ThFam
end
