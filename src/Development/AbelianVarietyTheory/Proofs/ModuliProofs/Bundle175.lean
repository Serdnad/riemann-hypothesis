module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle119
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle054
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Algebra.Order.PUnit
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PeriodObject

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun z i => ty i (a : E) * z i
      map_add' := fun z w => by funext i; simp [mul_add]
      map_smul' := fun c z => by funext i; simp [mul_left_comm] }
  map_one' := by ext z i; simp
  map_mul' a b := by
    ext z i
    show ty i ((a * b : 𝓞 E) : E) * _ = ty i (a : E) * (ty i (b : E) * _)
    push_cast
    rw [map_mul, _root_.mul_assoc]
  map_zero' := by ext z i; simp
  map_add' a b := by ext z i; simp [add_mul]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by simp [hermForm])
    (fun c z w => by simp [hermForm, smul_dotProduct])
    (fun z w w' => by simp [hermForm, Matrix.mulVec_add])
    (fun c z w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    {s : Set (Fin g → ℂ)} (hs : Submodule.span ℝ s = ⊤)
    (h : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have e : (imForm Hm).comp (F.restrictScalars ℝ) = (imForm Hm).compl₂ (F'.restrictScalars ℝ) :=
    LinearMap.ext_on hs fun z hz => LinearMap.ext_on hs fun w hw => h z hz w hw
  have im : ∀ z w, (hermForm Hm (F z) w).im = (hermForm Hm z (F' w)).im := fun z w =>
    LinearMap.congr_fun (LinearMap.congr_fun e z) w
  refine Complex.ext ?_ (im z w)
  have := im (Complex.I • z) w
  simpa [hermForm, smul_dotProduct] using this

theorem weilIs_of_lbIso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L (M.pull (𝟙 A : A ⟶ A).left)) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (hw : Out.WeilIs A M n x y c) : Out.WeilIs A L n x y c := by
  have h₁ : LBIso (lbPow L 1) (M.pull (𝟙 A : A ⟶ A).left) :=
    LBIso.trans (DVR.linComb_isLB _ hL _ _) hL (pull_isLB hM _) (lbIso_lbPow_one hL) h
  have := (weilIs_along_hom hG S A A (𝟙 A) L M 1 n T x y c c hA hA hL hM inferInstance h₁
    (by rwa [Category.comp_id, Category.comp_id])).1
  rwa [Nat.cast_one, _root_.mul_one] at this

theorem pelClass_of_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), 1 ≤ D.p + D.q → a w = H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) → IsPeriod D' ty Q → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → PELClass D a bas ρ em t := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D o _ g k J b em w w' a bas ρ ty t D' f ν Q Hm hpq hw hρ hty hgen hζ hper hpol
    ⟨u, χ, hAH, hΛ, _, hpt, hF⟩ hprim
  have := t.ab.comm
  have hQ : ∀ (c : 𝓞 E) x, diagAct ty c (Q x) = Q (c • x) := fun c x => funext fun i => (hper.1 c x i).symm
  have hkeep : ∀ c, ∀ z ∈ u.Λ, diagAct ty c z ∈ u.Λ := fun c z hz => by
    obtain ⟨x, rfl⟩ := (hΛ z).1 hz
    exact (hΛ _).2 ⟨c • x, (hQ c x).symm⟩
  obtain ⟨act, hact⟩ := GlobalTheory.T.exists_oAct_of_endo_preserving_lattice h₁ h₂ h₃ h₄ (𝓞 E) t.pol u (diagAct ty) hkeep
  change OAct (𝓞 E) t.A at act
  have hj : ∀ j, act.act (a j) = t.act j := fun j => by
    obtain ⟨F, hFQ, hFe⟩ := hF j
    have e : F.restrictScalars ℝ = (diagAct ty (a j)).restrictScalars ℝ :=
      LinearMap.ext_on_range hpol.2.2.1 fun x => (hFQ x).trans (hQ _ x).symm
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h₁ h₂ h₃ h₄ t.pol t.pol t.L t.L u u (diagAct ty (a j)) (hkeep _)).unique
      ⟨act.hom _, hact _⟩ ⟨t.hom j, fun z => ?_⟩
    exact (congrArg u.ex (LinearMap.congr_fun e z).symm).trans (hFe z)
  have hadj : ∀ c, LBIso (cubeLB t.A ![fst t.A t.A ≫ act.act c, snd t.A t.A] t.L)
      (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ act.act (H.bar c)] t.L) := fun c => by
    refine (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h₁ h₂ h₃ h₄ t.pol u Hm χ _ _ _ _ hAH (act.hom c) (act.hom (H.bar c)) (hact c)
      (hact (H.bar c))).2 (hermForm_adjoint_of_span Hm (diagAct ty c) (diagAct ty (H.bar c)) hpol.2.2.1 ?_)
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have e := D'.adj c x y
    rw [hQ, hQ, hpol.2.2.2.2.2, hpol.2.2.2.2.2, e]
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation h₁.globalFns E H _ t.A act t.L t.ab
    t.isLB (h₃ _ t.pol t.L t.isLB) hadj
  have iso' : LBIso PP.L (t.L.pull (𝟙 t.A : t.A ⟶ t.A).left) := by
    rw [← hw, hj] at iso
    refine LBIso.trans PP.isLB t.isLB (pull_isLB t.isLB _)
      (LBIso.trans PP.isLB (DVR.linComb_isLB _ t.isLB _ _) t.isLB iso hprim.2.2.symm) ?_
    exact (LBIso.chartPull (Geo.Tor.chartPullPull t.L (𝟙 _) (𝟙 _) rfl) (chartPullId t.L) (lbIso_refl t.isLB)).symm
  refine ⟨⟨t.A, isSemiAbelian_of_isAbelianScheme _ t.ab, act, PP, cub, sym, adj, prim⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t.A)), iso', fun j => ?_, fun K _ _ _ x β hx => ?_⟩
  · show act.act (a j) ≫ 𝟙 _ = 𝟙 _ ≫ t.act j
    rw [hj, Category.comp_id, Category.id_comp]
  obtain ⟨σ, rfl⟩ : ∃ σ : ℂ →+* K, x = spMap σ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain rfl : σ.comp em = β :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    have := b.unit.map em
    simp [h] at this
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_apply, hρ]
    exact GlobalTheory.T.determinantCondition_of_diagonalCMAction h₁ h₂ h₃ h₄ E H D t.pol u Hm χ act ty hAH hty hact K σ
  obtain ⟨I, hI⟩ := GlobalTheory.T.exists_tateIso_of_periodMap_genus_alt h₁ h₂ h₃ h₄ E H D D' f ν t.pol u Hm χ act Q hpq hgen hAH hpol.1 hΛ hpol.2.2.2.2.2
    (fun c n x => by
      rw [← hact, map_smul]
      exact congrArg (fun z => u.ex ((n : ℂ)⁻¹ • z)) (hQ c x).symm) K σ
  refine ⟨{ I with isom := fun n hn x y => weilIs_of_lbIso h₁.globalFns t.ab PP.isLB t.isLB iso' (I.isom n hn x y) },
    ?_, fun i => ?_⟩
  · rw [RingHom.comp_apply, hζ]
    exact (hI k hk).1
  · apply Over.OverMorphism.ext
    show (I.ev k _).left ≫ 𝟙 _ = spMap σ ≫ (t.pt i).left
    rw [Category.comp_id, hpt]
    exact (hI k hk).2 _

end GlobalTheory.PeriodObject
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem linear_eq_zero_of_mem_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) (z : Fin g → ℂ) : F z = 0 := by
  have hc : Continuous fun w => (⟨F w, h w⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
  simpa using congrArg Subtype.val this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm


open Matrix in
theorem exists_coord {g : ℕ} {La La' : Type} [AddCommGroup La] [AddCommGroup La'] (Q : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : La' ≃+ La) (Q' : La' →+ (Fin g → ℂ))
    (hQ : ∀ x, h (Q' x) = Q (e x)) (inj : Function.Injective Q) (disc : DiscreteTopology Q.range)
    (span : Submodule.span ℝ (Set.range Q) = ⊤) (herm : Hm.IsHermitian)
    (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Function.Injective Q' ∧ DiscreteTopology Q'.range ∧
      Submodule.span ℝ (Set.range Q') = ⊤ ∧ Hm'.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧
      ∀ x y, hermForm Hm' (Q' x) (Q' y) = hermForm Hm (Q (e x)) (Q (e y)) := by
  let L := h.toLinearMap
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, fun x y hxy => e.injective (inj (by rw [← hQ, ← hQ, hxy])), ?_, ?_,
    isHermitian_mul_mul_conjTranspose _ herm, fun z hz => ?_, fun x y => ?_⟩
  · let m : Q'.range → Q.range := fun z => ⟨h z, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨e x, (hQ x).symm⟩⟩
    have hm : Continuous m :=
      (L.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hm fun z w hzw =>
      Subtype.ext (h.injective (congrArg Subtype.val hzw))
  · have r : Set.range Q' = (h.symm.toLinearMap.restrictScalars ℝ) '' Set.range Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨e x, rfl⟩, by simp [← hQ]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e.symm x, h.injective (by simp [hQ])⟩
    rw [r, Submodule.span_image, span, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · rw [key]
    exact pos _ fun h0 => hz (h.injective (h0.trans (map_zero h).symm))
  · rw [key, ← hQ, ← hQ]
    rfl

theorem exists_module {O : Type} [CommRing O] {g : ℕ} {La : Type} [AddCommGroup La] (ty : Fin g → (O →+* ℂ))
    (Q : La →+ (Fin g → ℂ)) (inj : Function.Injective Q) (st : ∀ c x, ∃ y, ∀ i, Q y i = ty i c * Q x i) :
    ∃ _ : Module O La, ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := by
  choose sm hsm using st
  letI : SMul O La := ⟨sm⟩
  have hs : ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := hsm
  refine ⟨{ one_smul := fun x => inj (funext fun i => by simp [hs])
            mul_smul := fun c d x => inj (funext fun i => by simp [hs, _root_.mul_assoc])
            smul_zero := fun c => inj (funext fun i => by simp [hs])
            smul_add := fun c x y => inj (funext fun i => by simp [hs, mul_add])
            add_smul := fun c d x => inj (funext fun i => by simp [hs, add_mul])
            zero_smul := fun x => inj (funext fun i => by simp [hs]) }, hs⟩

theorem exists_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro l1 l2 l3 l4 E _ _ _ H D o _ g k J b em w w' a bas ρ ty t hw hw' hρ hty hP
  obtain ⟨La, _, EF, lam, ac, Q₀, Hm₀, hbij, hpol, -, u, χ, hAH, hΛ, hχ, hpt, hac⟩ :=
    GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta l1 l2 l3 l4 o g k J b em w w' t ((GlobalTheory.T.pelObjectClass_prim_and_iso_closed E H D o g k J b em w w' a bas ρ t hP).1 hw hw')
  obtain ⟨act, haj, hdet, hadj, I, hζ, hev⟩ := exists_act hP
  change OAct (𝓞 E) t.A at act
  rw [hρ] at hdet
  obtain ⟨h, hh⟩ : ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ (c : 𝓞 E) z,
      u.ex (h (fun i => ty i (c : E) * z i)) = u.ex (h z) ≫ act.act c :=
    GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition l1 l2 l3 l4 E H D t.pol u Hm₀ χ act ty hAH hty hdet
  obtain ⟨inj, disc, span, herm, pos, him⟩ := id hpol
  let F : 𝓞 E → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun c =>
    h.toLinearMap ∘ₗ (LinearMap.pi fun i => ty i (c : E) • LinearMap.proj i) ∘ₗ h.symm.toLinearMap
  have hF₀ : ∀ c z, F c z = h fun i => ty i (c : E) * h.symm z i := fun c z => rfl
  have hF : ∀ c z, u.ex (F c z) = u.ex z ≫ act.act c := fun c z => by
    have := hh c (h.symm z)
    rw [h.apply_symm_apply] at this
    exact this
  let Q₁ : La →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp Q₀
  have hQ₁ : ∀ x, h (Q₁ x) = Q₀ x := fun x => h.apply_symm_apply _
  obtain ⟨Hm₁, inj₁, disc₁, span₁, herm₁, pos₁, him₁⟩ :=
    exists_coord Q₀ Hm₀ h (AddEquiv.refl _) Q₁ hQ₁ inj disc span herm pos
  obtain ⟨_, hs⟩ := exists_module (fun i => (ty i).comp (algebraMap (𝓞 E) E)) Q₁ inj₁ (fun c x => by
    haveI := act.hom c
    have h1 : u.ex (Q₀ x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    have h2 : u.ex (F c (Q₀ x)) = 1 := by
      rw [hF, h1]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := (hΛ _).1 ((u.ker _).1 h2)
    refine ⟨y, fun i => ?_⟩
    show h.symm (Q₀ y) i = _
    rw [hy, hF₀, h.symm_apply_apply]
    rfl)
  have hs₀ : ∀ c x, Q₀ (c • x) = F c (Q₀ x) := fun c x => by
    rw [← hQ₁, hF₀]
    exact congrArg h (funext fun i => hs c x i)
  have adj : ∀ (c : 𝓞 E) x y, EF (c • x) y = EF x (H.bar c • y) := fun c x y => by
    have := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint l1 l2 l3 l4 t.pol u Hm₀ χ _ _ (F c) (F (H.bar c)) hAH (act.hom _) (act.hom _)
      (hF c) (hF _)).1 (hadj c) (Q₀ x) (Q₀ y)
    have h2 : ((EF (c • x) y : ℤ) : ℝ) = EF x (H.bar c • y) := by
      rw [← him, ← him, hs₀, hs₀]
      exact congrArg Complex.im this
    exact_mod_cast h2
  obtain ⟨D', e, hp, hq, hEF⟩ := GlobalTheory.PeriodDatum.exists_datum E H La EF D.p D.q g ty Q₁ Hm₁ hty hbij adj hs inj₁
    disc₁ span₁ herm₁ pos₁ (fun x y => by rw [him₁]; exact him x y)
  let Q₂ : D'.La →+ (Fin g → ℂ) := Q₀.comp e.toLinearMap.toAddMonoidHom
  have hQ₂ : ∀ x, Q₂ x = Q₀ (e x) := fun x => rfl
  obtain ⟨f, ν, hgen, hf⟩ := GlobalTheory.T.period_lattice_in_genus_alt l1 l2 l3 l4 E H D D' t.pol u Hm₀ χ act Q₂ hp hq hAH
    (inj.comp e.injective)
    (fun z => (hΛ z).trans ⟨fun ⟨x, hx⟩ => ⟨e.symm x, (congrArg Q₀ (e.apply_symm_apply x)).trans hx⟩,
      fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩)
    (fun x y => by rw [hEF]; exact him _ _)
    (fun c n x => by
      have := hF c ((n : ℂ)⁻¹ • Q₀ (e x))
      rw [map_smul, ← hs₀, ← map_smul e] at this
      exact this) I
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  obtain ⟨hζ', hev'⟩ := hf k (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hk))
  let Q : D'.La →+ (Fin g → ℂ) := Q₁.comp e.toLinearMap.toAddMonoidHom
  obtain ⟨Hm, inj', disc', span', herm', pos', him'⟩ :=
    exists_coord Q₀ Hm₀ h e.toAddEquiv Q (fun x => hQ₁ _) inj disc span herm pos
  have him'' : ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y := fun x y => by
    rw [him', hEF]; exact him _ _
  refine ⟨D', f, ν, Q, Hm, hgen, hζ.symm.trans hζ', ⟨fun c x i => ?_, inj', disc', span', Hm, herm', pos', him''⟩,
    ⟨inj', disc', span', herm', pos', him''⟩, ?_⟩
  · show Q₁ (e (c • x)) i = _ * Q₁ (e x) i
    rw [map_smul]
    exact hs _ _ _
  · refine GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates o g k J b em w w' t La EF lam ac Q₀ Hm₀ D'.La D'.EF
      (fun i => f k (bas (Pi.single i 1))) (fun j x => a j • x) Q Hm e.symm.toAddEquiv h.symm hpol
      ⟨inj', disc', span', herm', pos', him''⟩ (fun x => ?_) (fun x y => ?_) (fun j x => ?_) (fun i => ?_)
      ⟨u, χ, hAH, hΛ, hχ, hpt, hac⟩
    · show Q₁ (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl
    · show D'.EF (e.symm x) (e.symm y) = _
      rw [hEF, e.apply_symm_apply, e.apply_symm_apply]
    · show e.symm (ac j x) = a j • e.symm x
      rw [← map_smul]
      congr 1
      obtain ⟨G, hG, hG'⟩ := hac j
      haveI := u.discrete
      have h0 := linear_eq_zero_of_mem_discrete u.Λ (G - F (a j))
        (fun z => sub_mem_of_ex_eq u (by rw [hG', hF, haj])) (Q₀ x)
      apply inj
      rw [hs₀, ← hG]
      exact sub_eq_zero.1 h0
    · have h1 : u.ex ((k : ℂ)⁻¹ • Q₀ (lam i)) = u.ex ((k : ℂ)⁻¹ • Q₂ (f k (bas (Pi.single i 1)))) :=
        Over.OverMorphism.ext ((hpt i).symm.trans ((hev i).symm.trans (hev' _)))
      obtain ⟨y, hy⟩ := (hΛ _).1 (sub_mem_of_ex_eq u h1)
      refine ⟨e.symm y, e.injective (inj ?_)⟩
      show Q₀ (e (e.symm (lam i))) = Q₀ (e (f k (bas (Pi.single i 1)) + k • e.symm y))
      rw [e.apply_symm_apply, map_add (f := _), map_nsmul, e.apply_symm_apply, map_add (f := _), map_nsmul, hy, hQ₂, ← smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

end GlobalTheory.PELPeriod
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.NoTorus

theorem pmaps_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    PMaps (isoPullId (Geo.Tor.idIso L) hF) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  subst hF
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id]
  refine (gen_trans ht r z (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq)).trans
    (congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_))
  change _ = (gm (r ≫ φ k) z _ (res _ (L.g (p k) (q k)))) ^ ε k
  have hm : (r ≫ φ k) z ∈ (L.pull (𝟙 X)).U (fun _ => p k) ⊓ L.U (q k) := ⟨mem_pull.2 (hp' k), hq k⟩
  exact congrArg (fun u => u ^ ε k) (gm_res (r ≫ φ k) z _ hm (L.g (p k) (q k))).symm

theorem nonempty_isPullDeg_self {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    (D : DegData R I) : Nonempty (IsPullDeg (RingHom.id R) D.toPre D.toPre) := by
  have hgen {F : D.toPre.P.A.left ⟶ D.toPre.P.A.left} (hF : F = 𝟙 _) : PGen (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF) := by
    subst F
    intro Y f y j j' k k' hj hj' hk hk'
    have hgw : ∀ a b, f y ∈ D.toPre.P.L.U a → f y ∈ D.toPre.P.L.U b →
        gw (isoPullId (Geo.Tor.idIso D.toPre.P.L) rfl) f y a b =
          gm f y _ (D.toPre.P.L.g a b) := by
      intro a b ha hb
      have hm : f y ∈ (D.toPre.P.L.pull (𝟙 _)).U (fun _ => a) ⊓ D.toPre.P.L.U b := ⟨mem_pull.2 ha, hb⟩
      exact gm_res f y _ hm _
    rw [hgw j k hj hk, hgw j' k' hj' hk', Category.comp_id]
    have hV : f y ∈ (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') := ⟨⟨hj, hk⟩, ⟨hj', hk'⟩⟩
    have hw' : res (inf_le_left : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) (D.toPre.P.L.g j k) =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j ⊓ D.toPre.P.L.U j') (D.toPre.P.L.g j j') *
      (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U k ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g k k'))⁻¹ *
      res (inf_le_right : (D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') ≤ D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k') (D.toPre.P.L.g j' k') :=
      (idIso_isGen D.toPre.P.isLB) (j, k) (j', k')
    have key := congrArg (gm f y ((D.toPre.P.L.U j ⊓ D.toPre.P.L.U k) ⊓ (D.toPre.P.L.U j' ⊓ D.toPre.P.L.U k'))) hw'
    simp only [map_mul, map_inv, gm_res f y _ hV] at key
    exact key
  have : IsMonHom (Iso.refl D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.toPre.P.A))
  have gp : IsGrpPullback D.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) (Iso.refl D.toPre.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.toPre.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨W, hW, ⟨ψW⟩⟩ := psiOnExists R I hR D
  obtain ⟨hD, -⟩ := UnifUniq.exists_isPullDeg_id D.toPre D.toPre W hW ψW e me
    (isoPullId (Geo.Tor.idIso D.toPre.P.L) hF') ((isGen_iff _).2 (hgen hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (pmaps_id hF' (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => pmaps_id hF' (K := PUnit) (fun _ => D.toPre.xK x) (fun _ => -1) (D.toPre.psi_gen x))
  exact ⟨hD⟩

end GlobalTheory.NoTorus

namespace GlobalTheory

theorem isAbelianScheme_of_unif_of_subsingleton : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (IsLocalRing.maximalIdeal V) D A G → Subsingleton D.toPre.X → IsAbelianScheme G := by
  intro hL hL₂ V _ _ _ _ hc D A G _ hG hsa U hX
  have hR : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨A', eA, hA, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) D.toPre.P
  obtain ⟨hD⟩ := NoTorus.nonempty_isPullDeg_self hR D
  have hsemi : IsSemiAbelian D.toPre.P.A := by
    let B := D.toPre.P.A
    have hB := D.toPre.P.isAb
    have := hB.proper
    refine ⟨hB.comm, hB.smooth, inferInstance, inferInstance, hB.geomConnected, ?_⟩
    intro Ω _ _ p
    have hAb : IsAbelianScheme ((Over.pullback p).obj B) := by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd B.hom p); infer_instance
      · change IsProper (pullback.snd B.hom p); infer_instance
      · change GeometricallyConnected (pullback.snd B.hom p); infer_instance
    let A := (Over.pullback p).obj B
    have : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    exact ⟨{
      X := PUnit
      B := A
      isAbelian := hAb
      q := 𝟙 A
      q_hom := inferInstance
      q_flat := by rw [Over.id_left]; infer_instance
      q_surjective := by rw [Over.id_left]; infer_instance
      q_quasiCompact := by rw [Over.id_left]; infer_instance
      i := toUnit _ ≫ η
      i_hom := by have := hAb.comm; infer_instance
      isKernel := IsPullback.of_vert_isIso ⟨Category.comp_id _⟩ }⟩
  obtain ⟨ψ, -⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ V _ hR rfl D D A A' G D.toPre.P.A hsa
    hsemi U
    ⟨SelfUnif.selfPre D A' eA hA hw, fun k _ =>
      SelfUnif.expBij D A' eA hA hw hL.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩ hD
  have e : G.hom = ψ.inv.left ≫ D.toPre.P.A.hom := (Over.w ψ.inv).symm
  have := D.toPre.P.isAb.proper
  have : IsIso ψ.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψ.inv))
  exact ⟨hG, hsa.smooth, by rw [e]; infer_instance, hsa.geomConnected⟩

end GlobalTheory

end
end
