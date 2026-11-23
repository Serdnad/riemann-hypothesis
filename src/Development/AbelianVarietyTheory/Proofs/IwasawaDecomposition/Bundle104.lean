module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle091
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open Formalism.MainNotions.N

noncomputable section

namespace GlobalTheory.BrauerNesbittIrr

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

abbrev matHom (ρ : Γ →* GL (Fin a) k) : Γ →* Matrix (Fin a) (Fin a) k := (Units.coeHom _).comp ρ

abbrev liftRep (ρ : Γ →* GL (Fin a) k) : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin a) (Fin a) k :=
  MonoidAlgebra.lift k (Matrix (Fin a) (Fin a) k) Γ (matHom ρ)

theorem liftRep_mem (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k))
    (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) (α : MonoidAlgebra k Γ) :
    ∀ x ∈ W, liftRep ρ α *ᵥ x ∈ W := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => intro x _; simp [W.zero_mem]
  | add p q hp hq => intro x hx; rw [map_add (f := _), add_mulVec]; exact W.add_mem (hp x hx) (hq x hx)
  | single g c =>
    intro x hx
    rw [MonoidAlgebra.lift_single, Matrix.smul_mulVec]
    exact W.smul_mem c (hW g x hx)

theorem liftRep_surjective [IsAlgClosed k] (ρ : Γ →* GL (Fin a) k) (ha : 0 < a)
    (h : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Function.Surjective (liftRep ρ) := by
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hirr : IsIrrSub ρ ⊤ := ⟨top_ne_bot, fun g v _ => Submodule.mem_top,
    fun W' _ hinv => h W' hinv⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ hirr
  intro X
  have hle : Submodule.span k (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) ≤
      LinearMap.range (liftRep ρ).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, by simp⟩
  obtain ⟨α, hα⟩ := hle (hs ▸ Submodule.mem_top : X ∈ _)
  exact ⟨α, hα⟩

theorem irred_of_charpoly_eq [IsAlgClosed k] (ρ ρ' : Γ →* GL (Fin a) k)
    (hc : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ' g : Matrix (Fin a) (Fin a) k).charpoly)
    (h' : ∀ W : Submodule k (Fin a → k), (∀ g, ∀ x ∈ W, (ρ' g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (W : Submodule k (Fin a → k)) (hW : ∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin a) (Fin a) k) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨hb, ht⟩ := hne
  have hcp : ∀ α, (liftRep ρ α).charpoly = (liftRep ρ' α).charpoly :=
    GlobalTheory.charpoly_lift_eq_of_charpoly_eq a (matHom ρ) (matHom ρ') hc
  have hdet : ∀ α, (liftRep ρ α).det = (liftRep ρ' α).det := fun α => by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, hcp]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; exact absurd (Subsingleton.elim w 0) hw0
    · exact h
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hsurj := liftRep_surjective ρ' ha h'
  let S : Set (Matrix (Fin a) (Fin a) k) :=
    {X | ∃ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) ∧ liftRep ρ' α = X}
  let I : TwoSidedIdeal (Matrix (Fin a) (Fin a) k) := TwoSidedIdeal.mk' S
    ⟨0, fun x _ => by simp, by simp⟩
    (by
      rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
      exact ⟨α + β, fun x hx => by rw [map_add (f := _), add_mulVec, hα x hx, hβ x hx, add_zero],
        map_add _ _ _⟩)
    (by
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨-α, fun x hx => by rw [map_neg, neg_mulVec, hα x hx, neg_zero], map_neg _ _⟩)
    (by
      rintro X _ ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj X
      exact ⟨β * α, fun x hx => by rw [map_mul, ← mulVec_mulVec, hα x hx, mulVec_zero],
        map_mul _ _ _⟩)
    (by
      rintro _ Y ⟨α, hα, rfl⟩
      obtain ⟨β, rfl⟩ := hsurj Y
      exact ⟨α * β, fun x hx => by
        rw [map_mul, ← mulVec_mulVec, hα _ (liftRep_mem ρ W hW β x hx)], map_mul _ _ _⟩)
  have hmem : ∀ X, X ∈ I ↔ X ∈ S := fun X => TwoSidedIdeal.mem_mk' _ _ _ _ _ _ X
  rcases IsSimpleOrder.eq_bot_or_eq_top I with hI | hI
  · have h0 : ∀ α, (∀ x ∈ W, liftRep ρ α *ᵥ x = 0) → liftRep ρ' α = 0 := fun α hα => by
      have : liftRep ρ' α ∈ I := (hmem _).2 ⟨α, hα, rfl⟩
      rw [hI] at this
      exact (TwoSidedIdeal.mem_bot _).1 this
    let ψ : MonoidAlgebra k Γ →ₗ[k] (Fin (Module.finrank k W) → Fin a → k) :=
      { toFun := fun α i => liftRep ρ α *ᵥ ((Module.finBasis k W i : W) : Fin a → k)
        map_add' := fun α β => by funext i; simp [add_mulVec]
        map_smul' := fun c α => by funext i; simp [Matrix.smul_mulVec] }
    have hker : LinearMap.ker ψ ≤ LinearMap.ker (liftRep ρ').toLinearMap := by
      intro α hα
      rw [LinearMap.mem_ker] at hα ⊢
      apply h0 α
      intro x hx
      have hf : (Matrix.toLin' (liftRep ρ α)).comp W.subtype = 0 :=
        (Module.finBasis k W).ext fun i => by
          have := congrFun hα i
          simpa [ψ] using this
      have := LinearMap.congr_fun hf ⟨x, hx⟩
      simpa using this
    have hrange : LinearMap.range (liftRep ρ').toLinearMap = ⊤ := LinearMap.range_eq_top.2 hsurj
    let q := (LinearMap.ker ψ).liftQ (liftRep ρ').toLinearMap hker
    have hq : LinearMap.range q = ⊤ := by rw [Submodule.range_liftQ, hrange]
    haveI : FiniteDimensional k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) :=
      LinearEquiv.finiteDimensional (ψ.quotKerEquivRange).symm
    have h1 : Module.finrank k (Matrix (Fin a) (Fin a) k) ≤
        Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) := by
      have := LinearMap.finrank_range_le q
      rwa [hq, finrank_top] at this
    have h2 : Module.finrank k (MonoidAlgebra k Γ ⧸ LinearMap.ker ψ) ≤
        Module.finrank k W * a := by
      rw [ψ.quotKerEquivRange.finrank_eq]
      refine (Submodule.finrank_le _).trans (le_of_eq ?_)
      first
        | simp [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card]
        | rw [Module.finrank_pi_fintype]; simp
        | simp [Module.finrank_pi]
    have h3 : Module.finrank k W < a := by
      have := Submodule.finrank_lt ht
      simpa using this
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at h1
    nlinarith
  · have h1 : (1 : Matrix (Fin a) (Fin a) k) ∈ I := by rw [hI]; exact TwoSidedIdeal.mem_top _
    obtain ⟨κ, hκ, hκ1⟩ := (hmem _).1 h1
    have h0 : (liftRep ρ κ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hκ w hw⟩
    rw [hdet, hκ1, det_one] at h0
    exact one_ne_zero h0

theorem litBNIrr (Γ : Type) [Group Γ] : LitBNIrr Γ := by
  intro ℓ _ a ρ ρ' hc h' W hW
  exact irred_of_charpoly_eq ρ ρ' hc (fun W hW => h' W fun g _ x hx => hW g x hx) W
    (fun g x hx => hW g (Subgroup.mem_top g) x hx)

end GlobalTheory.BrauerNesbittIrr

end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem isSchemeTheoreticallyDominant_compl_of_effCartier :
    ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I →
      IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  intro W I hI
  choose U f hxU hf hIU using hI
  refine ⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · have h0 := Scheme.Hom.ideal_ker_le _ (U x) hs
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at h0
    have hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X := W) I.support.compl) ''ᵁ
        ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by
      intro y hy
      have hyU : y ∈ (U x).1 := W.basicOpen_le (f x) hy
      have hyc : y ∈ I.support.compl := by
        intro hy'
        have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
        rw [Scheme.mem_zeroLocus_iff] at this
        exact this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy
      exact ⟨⟨y, hyc⟩, hyU, rfl⟩
    have := (U x).2.isLocalization_basicOpen (f x)
    have hinj := IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x))
      ((Submonoid.powers_le).2 (hf x))
    have h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0 := by
      have h2 := congrArg (W.presheaf.map (homOfLE hle).op).hom h0
      have h3 := h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)
      refine Eq.trans ?_ h3
      erw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have : s = 0 := hinj (by rw [h1, map_zero])
    simp [this]

end GlobalTheory.ProjBlowup
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.adicCompletion_isDomain_and_isIntegrallyClosed : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], IsDomain (AdicCompletion (maximalIdeal A) A) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal A) A) := by
  first | exact @GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed <;> assumption)
end

section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor


theorem _root_.GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  first | exact @GlobalTheory.det_bounded_eTwoPi | exact GlobalTheory.det_bounded_eTwoPi | (intros; apply GlobalTheory.det_bounded_eTwoPi <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GlueLineBundle

variable {X W : Scheme.{0}}

def imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, j ''ᵁ V)ˣ :=
  Units.map (j.appIso V).inv.hom

theorem res_pull_imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) (v : Γ(W, V)ˣ) :
    res (j.preimage_image_eq V).ge (pullU j _ (imU j V v)) = v := by
  apply Units.ext
  have h := congrArg (fun q => q.hom v.val) (j.appIso_inv_appLE (U := V) (V := V) (j.preimage_image_eq V).ge)
  have e : (homOfLE (le_refl V)) = 𝟙 V := rfl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  show (W.presheaf.map (𝟙 (Opposite.op V))).hom v.val = v.val
  rw [W.presheaf.map_id]; rfl

theorem gm_imU (j : W ⟶ X) [IsOpenImmersion j] {Y : Scheme.{0}} (f : Y ⟶ W) (y : Y) (V : W.Opens)
    (hy : f y ∈ V) (v : Γ(W, V)ˣ) : gm (f ≫ j) y (j ''ᵁ V) (imU j V v) = gm f y V v := by
  have h1 : j (f y) ∈ j ''ᵁ V := j.apply_mem_image_iff.2 hy
  rw [← gm_pull f j y _ h1, ← gm_res f y (j.preimage_image_eq V).ge hy, res_pull_imU]

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}

theorem gm_id_val {O : X.Opens} {x : X} (hx : x ∈ O) (a : Γ(X, O)ˣ) :
    (gm (𝟙 X) x O a).val = X.presheaf.germ O x hx a.val := by
  rw [gm_val _ x O hx]; rfl

theorem unit_ext_imm {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by
  apply unit_ext
  intro x hx
  obtain ⟨W, j, hj, w, rfl, e⟩ := h x hx
  apply Units.ext
  rw [gm_id_val hx, gm_id_val hx]
  have e' := congrArg Units.val e
  rw [gm_val j w O hx, gm_val j w O hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective e'

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

abbrev NU (p : Σ a, (M a).ι) : X.Opens := (V p.1).ι ''ᵁ (M p.1).U p.2

def GSpec (p q : Σ a, (M a).ι) (u : Γ(X, NU V M p ⊓ NU V M q)ˣ) : Prop :=
  ∀ (c : A) (Y : Scheme.{0}) (f : Y ⟶ (V c).toScheme) (y : Y) (j l : (M c).ι),
    (⟨c, j⟩ : Σ a, (M a).ι) = p → (⟨c, l⟩ : Σ a, (M a).ι) = q → f y ∈ (M c).U j → f y ∈ (M c).U l →
    gm (f ≫ (V c).ι) y (NU V M p ⊓ NU V M q) u = gm f y ((M c).U j ⊓ (M c).U l) ((M c).g j l)

theorem mem_of_mem_NU {p : Σ a, (M a).ι} {x : X} (hx : x ∈ NU V M p) : x ∈ V p.1 :=
  Scheme.Opens.ι_image_le _ _ hx

theorem exists_gSpec (p q : Σ a, (M a).ι) : ∃ u, GSpec V M p q u := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, k⟩ := q
  by_cases hab : a = b
  · subst hab
    have hle : (V a).ι ''ᵁ (M a).U i ⊓ (V a).ι ''ᵁ (M a).U k ≤ (V a).ι ''ᵁ ((M a).U i ⊓ (M a).U k) :=
      fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx.1
        exact (V a).ι.apply_mem_image_iff.2 ⟨hw, (V a).ι.apply_mem_image_iff.1 hx.2⟩
    refine ⟨res hle (imU (V a).ι _ ((M a).g i k)), ?_⟩
    intro c Y f y j l h1 h2 hj hl
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain rfl := eq_of_heq h1'
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hm : (f ≫ (V c).ι) y ∈ (V c).ι ''ᵁ (M c).U j ⊓ (V c).ι ''ᵁ (M c).U l :=
      ⟨(V c).ι.apply_mem_image_iff.2 hj, (V c).ι.apply_mem_image_iff.2 hl⟩
    exact (gm_res (f ≫ (V c).ι) y hle hm _).trans (gm_imU (V c).ι f y ((M c).U j ⊓ (M c).U l) ⟨hj, hl⟩ _)
  · refine ⟨1, ?_⟩
    intro c Y f y j l h1 h2
    exact absurd ((Sigma.mk.inj_iff.1 h1).1.symm.trans (Sigma.mk.inj_iff.1 h2).1) hab

def glue : LB X where
  ι := Σ a, (M a).ι
  U := NU V M
  g p q := Classical.choose (exists_gSpec V M p q)

theorem gm_glue_g (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) :=
  Classical.choose_spec (exists_gSpec V M ⟨a, i⟩ ⟨a, k⟩) a Y f y i k rfl rfl hi hk

theorem gm_glue_g' (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  have := gm_glue_g V M a (𝟙 _) w i k hi hk
  rwa [Category.id_comp] at this

variable {V M}

theorem eq_of_mem (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b :=
  hdisj a b _ w.2 (mem_of_mem_NU V M h)

theorem glue_isLB (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hcov : ∀ x, ∃ a, x ∈ V a)
    (hM : ∀ a, (M a).IsLB) : (glue V M).IsLB := {
  cover := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha⟩ := hcov x
    obtain ⟨w, rfl⟩ : ∃ w : (V a).toScheme, (V a).ι w = x := ⟨⟨x, ha⟩, rfl⟩
    obtain ⟨i, hi⟩ := exists_chart (hM a) w
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, i⟩, (V a).ι.apply_mem_image_iff.2 hi⟩
  g_self p := by
    obtain ⟨a, i⟩ := p
    apply unit_ext_imm
    intro x hx
    have hx2 : x ∈ (V a).ι ''ᵁ (M a).U i := hx
    obtain ⟨w, hw, rfl⟩ := hx2
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ := hx
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [gm_res (V a).ι w _ hx', map_one, gm_glue_g' V M a w i i hw hw]
    exact gm_self (hM a) (𝟙 _) w hw
  cocycle p q r := by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, k⟩ := q
    obtain ⟨c, l⟩ := r
    apply unit_ext_imm
    intro x hx
    have h1 : x ∈ (V a).ι ''ᵁ (M a).U i := hx.1.1
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (V a).ι w ∈ NU V M ⟨b, k⟩ := hx.1.2
    have h3 : (V a).ι w ∈ NU V M ⟨c, l⟩ := hx.2
    have hb := eq_of_mem hdisj w h2
    have hc := eq_of_mem hdisj w h3
    subst hb hc
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ ⊓ (glue V M).U ⟨a, k⟩ ⊓ (glue V M).U ⟨a, l⟩ := hx
    have hk := (V a).ι.apply_mem_image_iff.1 h2
    have hl := (V a).ι.apply_mem_image_iff.1 h3
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [map_mul, gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_glue_g' V M a w i k hw hk,
      gm_glue_g' V M a w k l hk hl, gm_glue_g' V M a w i l hw hl]
    exact gm_cocycle (hM a) (𝟙 _) w hw hk hl }

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}

theorem exists_isoUnit (a : A) (J : PUnit → (glue V M).ι) (k : (M a).ι) :
    ∃ u : Γ((V a).toScheme, ((glue V M).pull (V a).ι).U J ⊓ (M a).U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ (V a).toScheme) (y : Y) (i : (M a).ι),
        J PUnit.unit = (⟨a, i⟩ : Σ a, (M a).ι) → f y ∈ (M a).U i → f y ∈ (M a).U k →
        gm f y _ u = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  by_cases h : ∃ i' : (M a).ι, J PUnit.unit = (⟨a, i'⟩ : Σ a, (M a).ι)
  · obtain ⟨i', hi'⟩ := h
    have hle : ((glue V M).pull (V a).ι).U J ⊓ (M a).U k ≤ (M a).U i' ⊓ (M a).U k := fun w hw => by
      have h1 : (V a).ι w ∈ (glue V M).U (J PUnit.unit) := mem_pull.1 hw.1
      rw [hi'] at h1
      exact ⟨(V a).ι.apply_mem_image_iff.1 h1, hw.2⟩
    refine ⟨res hle ((M a).g i' k), fun Y f y i hJ hi hk => ?_⟩
    obtain rfl := sigma_mk_injective (hi'.symm.trans hJ)
    have hm : f y ∈ ((glue V M).pull (V a).ι).U J ⊓ (M a).U k := by
      refine ⟨mem_pull.2 ?_, hk⟩
      show (V a).ι (f y) ∈ (glue V M).U (J PUnit.unit)
      rw [hi']
      exact (V a).ι.apply_mem_image_iff.2 hi
    exact gm_res f y hle hm _
  · exact ⟨1, fun Y f y i hJ => absurd ⟨i, hJ⟩ h⟩

def isoGen (a : A) : LB.Iso (M a) ((glue V M).pull (V a).ι) :=
  ⟨fun p => Classical.choose (exists_isoUnit a p.1 p.2)⟩

theorem pgen_isoGen (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨b, i⟩ := j
  obtain ⟨b', i'⟩ := j'
  have hb : a = b := eq_of_mem hdisj (f y) hj
  have hb' : a = b' := eq_of_mem hdisj (f y) hj'
  subst hb hb'
  have hi : f y ∈ (M a).U i := (V a).ι.apply_mem_image_iff.1 hj
  have hi' : f y ∈ (M a).U i' := (V a).ι.apply_mem_image_iff.1 hj'
  have e1 : gw (isoGen a) f y ⟨a, i⟩ k = gm f y _ ((M a).g i k) :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i⟩) k) Y f y i rfl hi hk
  have e2 : gw (isoGen a) f y ⟨a, i'⟩ k' = gm f y _ ((M a).g i' k') :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i'⟩) k') Y f y i' rfl hi' hk'
  rw [e1, e2, gm_glue_g V M a f y i i' hi hi', mul_right_comm, gm_cocycle (hM a) f y hi hi' hk',
    ← gm_cocycle (hM a) f y hi hk hk', mul_inv_cancel_right]

end GlobalTheory.GlueLineBundle


open GlobalTheory.GlueLineBundle in
theorem GlobalTheory.glue_lineBundles : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  intro X A V hdisj hcov M hM
  exact ⟨glue V M, glue_isLB hdisj hcov hM, fun a =>
    LBIso.symm ⟨isoGen a, (isGen_iff _).2 (pgen_isoGen hdisj hM a)⟩⟩
end
end
