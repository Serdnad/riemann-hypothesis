module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle057
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Monoidal.Mon
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle050
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle015

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.DimShift

variable {R : Type} [CommRing R]

def h0ι (K : CochainComplex (ModuleCat.{0} R) ℕ) : K.homology 0 ⟶ K.X 0 :=
  K.isoHomologyπ₀.inv ≫ K.iCycles 0

instance h0ι_mono (K : CochainComplex (ModuleCat.{0} R) ℕ) : Mono (h0ι K) := by
  unfold h0ι
  infer_instance

theorem h0ι_d (K : CochainComplex (ModuleCat.{0} R) ℕ) : h0ι K ≫ K.d 0 1 = 0 := by
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

theorem h0ι_lift (K : CochainComplex (ModuleCat.{0} R) ℕ) {A : ModuleCat.{0} R} (f : A ⟶ K.X 0)
    (hf : f ≫ K.d 0 1 = 0) : ∃ g : A ⟶ K.homology 0, g ≫ h0ι K = f := by
  refine ⟨K.liftCycles f 1 (CochainComplex.next ℕ 0) hf ≫ K.isoHomologyπ₀.hom, ?_⟩
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.liftCycles_i]

theorem h0ι_naturality {K L : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ L) :
    HomologicalComplex.homologyMap φ 0 ≫ h0ι L = h0ι K ≫ φ.f 0 := by
  unfold GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality, Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]

theorem exists_h0_iso (K L : CochainComplex (ModuleCat.{0} R) ℕ) (ε : K.X 0 ≅ L.X 0)
    (h : ∀ x : K.X 0, (K.d 0 1).hom x = 0 ↔ (L.d 0 1).hom (ε.hom.hom x) = 0) :
    ∃ e : K.homology 0 ≅ L.homology 0, e.hom ≫ h0ι L = h0ι K ≫ ε.hom := by
  have hK : ∀ x, (K.d 0 1).hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K).hom x) = 0 := fun x => by
    have := congrArg (fun φ => ModuleCat.Hom.hom φ x) (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_d K)
    first
      | exact this
      | simpa using this
  have hL : ∀ y, (L.d 0 1).hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y) = 0 := fun y => by
    have := congrArg (fun φ => ModuleCat.Hom.hom φ y) (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_d L)
    first
      | exact this
      | simpa using this
  have h1 : (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K ≫ ε.hom) ≫ L.d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    first
      | exact (h _).1 (hK x)
      | simpa using (h _).1 (hK x)
  have h2 : (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L ≫ ε.inv) ≫ K.d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have hε : ε.hom.hom (ε.inv.hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y)) = (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y := by
      show (ε.inv ≫ ε.hom).hom _ = _
      rw [ε.inv_hom_id]
      rfl
    have := (h (ε.inv.hom ((GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L).hom y))).2 (by rw [hε]; exact hL y)
    first
      | exact this
      | simpa using this
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_lift L (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K ≫ ε.hom) h1
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_lift K (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L ≫ ε.inv) h2
  refine ⟨⟨f₁, f₂, ?_, ?_⟩, hf₁⟩
  · rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι K), Category.assoc, hf₂, ← Category.assoc, hf₁]
    simp
  · rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι L), Category.assoc, hf₁, ← Category.assoc, hf₂]
    simp

theorem nonempty_iso_of_middle_isZero {S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)}
    (hS : S.ShortExact) (k : ℕ) (h₁ : IsZero (S.X₂.homology (k + 1)))
    (h₂ : IsZero (S.X₂.homology (k + 2))) :
    Nonempty (S.X₃.homology (k + 1) ≅ S.X₁.homology (k + 2)) := by
  have r : (ComplexShape.up ℕ).Rel (k + 1) (k + 2) := rfl
  haveI : Mono (hS.δ (k + 1) (k + 2) r) :=
    (hS.homology_exact₃ (k + 1) (k + 2) r).mono_g (h₁.eq_of_src _ _)
  haveI : Epi (hS.δ (k + 1) (k + 2) r) :=
    (hS.homology_exact₁ (k + 1) (k + 2) r).epi_f (h₂.eq_of_tgt _ _)
  haveI : IsIso (hS.δ (k + 1) (k + 2) r) := isIso_of_mono_of_epi _
  exact ⟨asIso (hS.δ (k + 1) (k + 2) r)⟩

theorem nonempty_iso_h1 {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (z₁ : IsZero (S₁.X₂.homology 1)) (z₂ : IsZero (S₂.X₂.homology 1))
    (eI : S₁.X₂.homology 0 ≅ S₂.X₂.homology 0) (eQ : S₁.X₃.homology 0 ≅ S₂.X₃.homology 0)
    (w : HomologicalComplex.homologyMap S₁.g 0 ≫ eQ.hom =
      eI.hom ≫ HomologicalComplex.homologyMap S₂.g 0) :
    Nonempty (S₁.X₁.homology 1 ≅ S₂.X₁.homology 1) := by
  have hr : (ComplexShape.up ℕ).Rel 0 1 := rfl
  haveI : Epi (hS₁.δ 0 1 hr) := (hS₁.homology_exact₁ 0 1 hr).epi_f (z₁.eq_of_tgt _ _)
  haveI : Epi (hS₂.δ 0 1 hr) := (hS₂.homology_exact₁ 0 1 hr).epi_f (z₂.eq_of_tgt _ _)
  have hc₁ := (hS₁.homology_exact₃ 0 1 hr).gIsCokernel
  have hc₂ := (hS₂.homology_exact₃ 0 1 hr).gIsCokernel
  have w' : HomologicalComplex.homologyMap S₂.g 0 ≫ eQ.inv =
      eI.inv ≫ HomologicalComplex.homologyMap S₁.g 0 := by
    rw [← cancel_epi eI.hom, ← Category.assoc, ← w]
    simp
  obtain ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' hc₁ (eQ.hom ≫ hS₂.δ 0 1 hr) (by
    show HomologicalComplex.homologyMap S₁.g 0 ≫ eQ.hom ≫ hS₂.δ 0 1 hr = 0
    rw [← Category.assoc, w, Category.assoc, hS₂.comp_δ 0 1 hr, comp_zero])
  obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' hc₂ (eQ.inv ≫ hS₁.δ 0 1 hr) (by
    show HomologicalComplex.homologyMap S₂.g 0 ≫ eQ.inv ≫ hS₁.δ 0 1 hr = 0
    rw [← Category.assoc, w', Category.assoc, hS₁.comp_δ 0 1 hr, comp_zero])
  have hφ' : hS₁.δ 0 1 hr ≫ φ = eQ.hom ≫ hS₂.δ 0 1 hr := hφ
  have hψ' : hS₂.δ 0 1 hr ≫ ψ = eQ.inv ≫ hS₁.δ 0 1 hr := hψ
  refine ⟨⟨φ, ψ, ?_, ?_⟩⟩
  · rw [← cancel_epi (hS₁.δ 0 1 hr), ← Category.assoc, hφ', Category.assoc, hψ']
    simp
  · rw [← cancel_epi (hS₂.δ 0 1 hr), ← Category.assoc, hψ', Category.assoc, hφ']
    simp

theorem homology_nonempty_iso : ∀ {R : Type} [CommRing R] {𝒜 : Type 1} [Category.{0} 𝒜] [HasZeroMorphisms 𝒜]
    (T₁ T₂ : 𝒜 ⥤ CochainComplex (ModuleCat.{0} R) ℕ) [T₁.PreservesZeroMorphisms] [T₂.PreservesZeroMorphisms]
    (ε : ∀ G, (T₁.obj G).X 0 ≅ (T₂.obj G).X 0),
    (∀ {G G' : 𝒜} (φ : G ⟶ G'), (T₁.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ (T₂.map φ).f 0) →
    (∀ (G : 𝒜) (x : (T₁.obj G).X 0),
      ((T₁.obj G).d 0 1).hom x = 0 ↔ ((T₂.obj G).d 0 1).hom ((ε G).hom.hom x) = 0) →
    (∀ G : 𝒜, ∃ (I Q : 𝒜) (i : G ⟶ I) (p : I ⟶ Q) (w : i ≫ p = 0),
      ((ShortComplex.mk i p w).map T₁).ShortExact ∧ ((ShortComplex.mk i p w).map T₂).ShortExact ∧
      ∀ n, IsZero ((T₁.obj I).homology (n + 1)) ∧ IsZero ((T₂.obj I).homology (n + 1))) →
    ∀ (n : ℕ) (G : 𝒜), Nonempty ((T₁.obj G).homology n ≅ (T₂.obj G).homology n) := by
  intro R _ 𝒜 _ _ T₁ T₂ _ _ ε hnat hker hres
  have h0 : ∀ G, ∃ e : (T₁.obj G).homology 0 ≅ (T₂.obj G).homology 0,
      e.hom ≫ GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₂.obj G) = GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₁.obj G) ≫ (ε G).hom :=
    fun G => GlobalTheory.CompanionTheory.Hodge.DimShift.exists_h0_iso _ _ (ε G) (hker G)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G
    obtain ⟨I, Q, i, p, w, hS₁, hS₂, hI⟩ := hres G
    rcases n with _ | _ | k
    · obtain ⟨e, -⟩ := h0 G
      exact ⟨e⟩
    · obtain ⟨eI, heI⟩ := h0 I
      obtain ⟨eQ, heQ⟩ := h0 Q
      refine GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_h1 hS₁ hS₂ (hI 0).1 (hI 0).2 eI eQ ?_
      show HomologicalComplex.homologyMap (T₁.map p) 0 ≫ eQ.hom =
        eI.hom ≫ HomologicalComplex.homologyMap (T₂.map p) 0
      rw [← cancel_mono (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι (T₂.obj Q))]
      simp only [Category.assoc, heQ, GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_naturality,
        reassoc_of% (GlobalTheory.CompanionTheory.Hodge.DimShift.h0ι_naturality (T₁.map p)), reassoc_of% heI, hnat]
    · obtain ⟨a⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_of_middle_isZero hS₁ k (hI k).1 (hI (k + 1)).1
      obtain ⟨b⟩ := GlobalTheory.CompanionTheory.Hodge.DimShift.nonempty_iso_of_middle_isZero hS₂ k (hI k).2 (hI (k + 1)).2
      obtain ⟨c⟩ := ih (k + 1) (by omega) Q
      exact ⟨a.symm ≪≫ c ≪≫ b⟩

end GlobalTheory.CompanionTheory.Hodge.DimShift
end
end

section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_dotProduct_eq_one :
    ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (a : Fin (n + 1) → k), a ≠ 0 →
  Fintype.card k * (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  intro k _ _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  have hax₀ : a ⬝ᵥ Pi.single i (a i)⁻¹ = 1 := by
    rw [dotProduct_single, mul_inv_cancel₀ hi]
  have hfib : ∀ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card =
      (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1)).card := by
    intro c
    apply Finset.card_bij' (fun x _ => x + (1 - c) • Pi.single i (a i)⁻¹)
      (fun x _ => x - (1 - c) • Pi.single i (a i)⁻¹)
    case hi =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_add, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case hj =>
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [dotProduct_sub, dotProduct_smul, hax₀, hx, smul_eq_mul, mul_one]
      ring
    case left_inv =>
      intro x _
      simp
    case right_inv =>
      intro x _
      simp
  have htot : (Finset.univ : Finset (Fin (n + 1) → k)).card =
      ∑ c : k, (Finset.univ.filter (fun x : Fin (n + 1) → k => a ⬝ᵥ x = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (a ⬝ᵥ x))
  have hcard : (Finset.univ : Finset (Fin (n + 1) → k)).card = Fintype.card k ^ (n + 1) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [← hcard, htot, Finset.sum_congr rfl (fun c _ => hfib c), Finset.sum_const,
    Finset.card_univ, smul_eq_mul]

end GlobalTheory.CompanionTheory.GapOpCount
end

section

open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

noncomputable def pairMap {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₗ[k] k × k where
  toFun x := (a ⬝ᵥ x, b ⬝ᵥ x)
  map_add' x y := by simp [dotProduct_add]
  map_smul' c x := by simp [dotProduct_smul]

theorem pairMap_range {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hform : ∀ u v : k, φ (u, v) = u * φ (1, 0) + v * φ (0, 1) := by
    intro u v
    have h : ((u, v) : k × k) = u • ((1, 0) : k × k) + v • ((0, 1) : k × k) := by simp
    rw [h, map_add (f := _), map_smul, map_smul]
    simp
  have hzero : (φ (1, 0) • a + φ (0, 1) • b) = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : φ (pairMap a b x) = 0 := hle (LinearMap.mem_range_self _ x)
    have hx' : φ (a ⬝ᵥ x, b ⬝ᵥ x) = 0 := hx
    rw [hform] at hx'
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    linear_combination hx'
  by_cases hμ : φ (0, 1) = 0
  · rw [hμ, zero_smul, add_zero] at hzero
    rcases smul_eq_zero.mp hzero with hl | h0
    · apply hφ
      ext p
      · simp [hl]
      · simp [hμ]
    · exact ha h0
  · apply hb (-(φ (0, 1))⁻¹ * φ (1, 0))
    have h1 : φ (0, 1) • b = -(φ (1, 0) • a) := eq_neg_of_add_eq_zero_right hzero
    calc b = (φ (0, 1))⁻¹ • (φ (0, 1) • b) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = (-(φ (0, 1))⁻¹ * φ (1, 0)) • a := by
        rw [h1, smul_neg, smul_smul, neg_mul, neg_smul]

theorem card_two_equations (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  have hr := pairMap_range a b ha hb
  obtain ⟨x0, hx0⟩ : ∃ x0, pairMap a b x0 = ((1, 1) : k × k) := by
    have : ((1, 1) : k × k) ∈ LinearMap.range (pairMap a b) := by rw [hr]; trivial
    exact this
  have hx1 : a ⬝ᵥ x0 = 1 := congrArg Prod.fst hx0
  have hx2 : b ⬝ᵥ x0 = 1 := congrArg Prod.snd hx0
  have hker : ∀ y, y ∈ LinearMap.ker (pairMap a b) ↔ a ⬝ᵥ y = 0 ∧ b ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker]
    exact Prod.ext_iff
  let e : LinearMap.ker (pairMap a b) ≃ {x : Fin (n + 1) → k // a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1} :=
    { toFun := fun y => ⟨y.1 + x0, by
        have h := (hker y.1).1 y.2
        simp [dotProduct_add, h.1, h.2, hx1, hx2]⟩
      invFun := fun x => ⟨x.1 - x0, by
        rw [hker]
        simp [dotProduct_sub, x.2.1, x.2.2, hx1, hx2]⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  have hcard : (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card
      = Fintype.card k ^ Module.finrank k (LinearMap.ker (pairMap a b)) := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (pairMap a b)),
      Fintype.card_congr e, Fintype.card_subtype]
  have hrank := LinearMap.finrank_range_add_finrank_ker (pairMap a b)
  rw [hr, finrank_top] at hrank
  have h2 : Module.finrank k (k × k) = 2 := by simp
  have hV : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
  rw [h2, hV] at hrank
  rw [hcard, ← pow_add, hrank]

end GlobalTheory.CompanionTheory.GapOpCount
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

section Lat

variable (K : Type) [Field K] [NumberField K]

def intVec (m : ℕ) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {v | ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = v i}
  add_mem' := by
    intro v w hv hw i
    obtain ⟨o, ho⟩ := hv i
    obtain ⟨p, hp⟩ := hw i
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨o, ho⟩ := hv i
    exact ⟨a * o, by simp [ho, Algebra.smul_def]⟩

abbrev FQ : Type := (Fin 1 → K) ⧸ intVec K 1

def den (x : K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) (FQ K) (Submodule.Quotient.mk fun _ => x)

def idx (c : Submodule (𝓞 K) K) : ℕ :=
  (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex c.toAddSubgroup

def zetaR (r : ℝ) : ℝ := ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-r)

variable {K}

def lam {m : ℕ} (c : Matrix (Fin m) (Fin m) K) : Submodule (𝓞 K) (Fin m → K) :=
  intVec K m ⊔ (intVec K m).map (c.mulVecLin.restrictScalars (𝓞 K))

def IsLat {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def tor {m : ℕ} (c : Matrix (Fin m) (Fin m) K) (u : Fin m → K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ lam c) (Submodule.Quotient.mk u)

def lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule (𝓞 K) K :=
  (lam C).comap (LinearMap.single (𝓞 K) (fun _ : Fin (m + 1) => K) (Fin.last m))

theorem isLat_intVec (m : ℕ) : IsLat (intVec K m) := by
  refine ⟨?_, ?_⟩
  · have h : intVec K m = (⊤ : Submodule (𝓞 K) (Fin m → 𝓞 K)).map
        (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin m)) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      constructor
      · intro hv
        choose o ho using hv
        exact ⟨o, funext fun i => ho i⟩
      · rintro ⟨o, rfl⟩ i
        exact ⟨o i, rfl⟩
    rw [h]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : K) : Fin m → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro j
    by_cases h : j = i
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h]⟩

end Lat

section GlobalTheory

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := fun i j =>
  Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) d (fun b => σ (u b)) j)
    (fun a => Fin.lastCases (motive := fun _ => E) (u a) (fun b => c a b) j) i

variable [NumberField E]

def sO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

end GlobalTheory

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section

open Matrix GlobalTheory.CompanionTheory.Jp

theorem _root_.GlobalTheory.T.card_completions_to_full_rank : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | exact GlobalTheory.CompanionTheory.Jp.CntCols.card_completions | (intros; apply GlobalTheory.CompanionTheory.Jp.CntCols.card_completions <;> assumption)
end

section

namespace GlobalTheory.CompanionTheory.ZModDual

theorem nat_card_dual_eq : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by
  intro n _ N _ _ _
  exact GlobalTheory.ZModDual.card_dual_eq n N

end GlobalTheory.CompanionTheory.ZModDual
end
