module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle039
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle022
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle013
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SectionBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.RatElt

theorem hform_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ g * J * g) x y := by
  have h : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; exact RingHom.map_mulVec σ g x i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (σ ∘ x) (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have h : σ ∘ (Pi.single i 1 : Fin n → A) = Pi.single i 1 := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  rw [hform_eq, h]; simp

theorem mem_UJ_iff {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (g : GL (Fin n) A) :
    g ∈ Formalism.UG.UJ σ J ↔ ∀ x y, Formalism.UG.hform σ J ((g : Matrix (Fin n) (Fin n) A) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) = Formalism.UG.hform σ J x y := by
  change Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hform_single, hform_single] at this

theorem bc_mem_HR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [Nontrivial R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E) :
    Formalism.UG.bc (inclR (F := F) R) g ∈ HR R σ J ↔ g ∈ Formalism.UG.UJ (σ : E →+* E) J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) R) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have hc : Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) =
      (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j; simp [Formalism.UG.cT, sigR, inclR]
  change Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) = J.map (inclR (F := F) R) ↔
    Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective hinj).eq_iff

theorem bc_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
    [CommRing S] [Algebra F S] (φ : R →ₐ[F] S) {n : ℕ} (g : GL (Fin n) E) :
    (Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g)).1 =
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) S) := by
  ext i j
  simp [Formalism.UG.bc, inclR]

variable {D : D7}

theorem herm_eq (V : HSp D) (x y : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) x y = - Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram y x := by
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change x b * (-V.gram a b) * cc (y a) = -(cc (y a) * V.gram a b * x b)
  ring

theorem herm_iff (V : HSp D) (g : GL (Fin V.rank) D.host.E) :
    (∀ u v, herm (-V.gramᵀ) ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u)
      ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) ↔
    Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  rw [bc_mem_HR_iff, mem_UJ_iff]
  simp only [herm_eq, neg_inj]
  exact forall_comm

theorem fin_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (finHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
  unfold finHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem inf_eq {V : HSp D} {γ : GA D V} {γ' : GL (Fin V.rank) D.host.E} (h : IsRat V γ γ') :
    (infHom V γ).1 = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Ainf D.host.F)) := by
  unfold infHom IsRat at *
  rw [MonoidHom.comp_apply, h]
  exact bc_map_incl _ _

theorem rational_elements : ∀ (D : D7) (V : HSp D), (∀ γ, γ ∈ GQ V ↔ ∃ γ', IsRat V γ γ') ∧ (∀ γ γ', IsRat V γ γ' → (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v)) ∧ (∀ γ' : GL (Fin V.rank) D.host.E, (∀ u v, herm (-V.gramᵀ) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ u) ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = herm (-V.gramᵀ) u v) → ∃ γ, IsRat V γ γ') ∧ (∀ γ γ' δ δ', IsRat V γ γ' → IsRat V δ δ' → IsRat V (γ * δ) (γ' * δ') ∧ IsRat V γ⁻¹ γ'⁻¹) ∧ ∀ γ γ', IsRat V γ γ' → (∀ v, (finHom V γ).1 *ᵥ finVec V v = finVec V ((γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v)) ∧ ∀ τ θ, Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → archM V θ γ = (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ := by
  intro D V
  have hmem : ∀ γ γ', IsRat V γ γ' → Formalism.UG.bc (incA D) γ' ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro γ γ' h
    rw [← h]; exact γ.2
  have : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  refine ⟨fun γ => ⟨?_, ?_⟩, fun γ γ' h => (herm_iff V γ').2 (hmem γ γ' h),
    fun γ' h => ⟨⟨_, (herm_iff V γ').1 h⟩, rfl⟩, fun γ γ' δ δ' h k => ⟨?_, ?_⟩, fun γ γ' h => ⟨fun v => ?_, fun τ θ hθ => ?_⟩⟩
  · rintro ⟨γ', -, h⟩
    exact ⟨γ', h.symm⟩
  · rintro ⟨γ', h⟩
    exact ⟨γ', (bc_mem_HR_iff _ _ _ _).1 (hmem γ γ' h), h.symm⟩
  · unfold IsRat at *
    rw [map_mul, map_mul, h, k]
  · unfold IsRat at *
    rw [map_inv, map_inv, h]
  · rw [fin_eq h]
    funext i
    exact (RingHom.map_mulVec (inclR (F := D.host.F) (Af D.host.F))
      (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) v i).symm
  · unfold archM
    rw [inf_eq h]
    ext i j
    exact hθ.1 _

end GlobalTheory.Member.RatElt
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincTransv

theorem transv_mem_princ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∃ m : ℕ, 0 < m ∧ ∀ κ0 : E, (κ0 = 2 * ξ₀ ∨ κ0 = -(2 * ξ₀)) → ∀ ξ ∈ LinearMap.range φ0, herm Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s → ∃ γ ∈ princ l Gm Di φ0, (γ : Matrix (Fin r) (Fin r) E) = transvMat Gm ξ ((m : E) * s * κ0) := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 hξ h
  have hξ' : IsCMField.complexConj E ξ₀ = -ξ₀ := hξ
  have hG := h.2.2.1
  have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H Di r (-ξ₀) Gm φ0
    (by simp [cc, hξ']) h).2.2.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  set d : ℕ := (NumberField.discr E).natAbs with hd
  have hd0 : 0 < d := Int.natAbs_pos.2 (NumberField.discr_ne_zero E)
  refine ⟨l.M * l.A * d, Nat.mul_pos (Nat.mul_pos hM l.A_pos) hd0, ?_⟩
  intro κ0 hκ ξ hξΛ hiso s hs hsi
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have hs' : IsCMField.complexConj E s = s := hs
  set α : E := ((l.M * l.A * d : ℕ) : E) * s * κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hs', hκc]
  have h2 : IsIntegral ℤ (2 : E) := isIntegral_natCast 2
  have hint' : ∀ v ∈ LinearMap.range φ0, IsIntegral ℤ ((d : E) * κ0 * herm Gm v ξ) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hξΛ
    have h1 := h2.mul (hint x y)
    have hdd : (d : E) = (NumberField.discr E : E) ∨ (d : E) = -(NumberField.discr E : E) := by
      rcases Int.natAbs_eq (NumberField.discr E) with h | h
      · left; rw [h, Int.cast_natCast]
      · right; rw [h, Int.cast_neg, Int.cast_natCast, neg_neg]
    have hpm : (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y))) ∨
        (d : E) * κ0 * herm Gm (φ0 x) (φ0 y) =
          -(2 * ((NumberField.discr E : E) * (-ξ₀ * herm Gm (φ0 x) (φ0 y)))) := by
      rcases hdd with e | e <;> rcases hκ with e' | e' <;> rw [e, e']
      · right; ring
      · left; ring
      · left; ring
      · right; ring
    rcases hpm with e | e <;> rw [e]
    · exact h1
    · exact h1.neg
  have key : ∀ v ∈ LinearMap.range φ0,
      (s * ((d : E) * κ0 * herm Gm v ξ)) • ξ ∈ LinearMap.range φ0 := fun v hv =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _ (hsi.mul (hint' v hv)) hξΛ
  have e : ∀ v, (α * herm Gm v ξ) • ξ =
      (l.M * l.A) • ((s * ((d : E) * κ0 * herm Gm v ξ)) • ξ) := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, hαdef]
    congr 1
    push_cast
    ring
  refine ⟨GlobalTheory.FlagData.transv Gm hiso α, ⟨⟨GlobalTheory.FlagData.herm_transvMat hG hiso hα, fun x => ?_⟩,
    fun a _ => ?_, fun a => ?_⟩, rfl⟩
  · change x ∈ LinearMap.range φ0 ↔ transvMat Gm ξ α *ᵥ x ∈ LinearMap.range φ0
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (by rw [e]; exact nsmul_mem (key x hx) _), fun hx => ?_⟩
    have h := nsmul_mem (key _ hx) (l.M * l.A)
    rw [← e, GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.A • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_smul]
  · obtain ⟨b, hb⟩ := key _ (LinearMap.mem_range_self φ0 a)
    refine ⟨l.M • b, ?_⟩
    change transvMat Gm ξ α *ᵥ φ0 a = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, e, ← hb, map_nsmul, mul_comm, mul_smul]

end GlobalTheory.PrincTransv
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolChart

theorem isHolTo_congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a a' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) (he : ∀ b ∈ B, a' b = a b) : IsHolTo B a' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [he b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩

theorem valAt'_spMap {R : Type} [CommRing R] (ψ : R →+* ℂ) (t : R) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) = ψ t := by
  have h : ⊤ ≤ (spMap ψ) ⁻¹ᵁ ⊤ := le_top
  rw [valAt', dif_pos h, valAt]
  have e : (spMap ψ).appLE ⊤ ⊤ h = (spMap ψ).appTop := (spMap ψ).appLE_eq_app
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)
  have n' := congrArg (fun φ => φ.hom t) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
  rw [e]
  erw [← n']
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply _

theorem exists_coordinates {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {X : Scheme.{0}}
    {a : V → (Sp ℂ ⟶ X)} (h : IsHolTo B a) {R : Type} [CommRing R] (j : Sp R ⟶ X) [IsOpenImmersion j]
    {b₀ : V} (hb₀ : b₀ ∈ B) (hj : a b₀ (default : PrimeSpectrum ℂ) ∈ Set.range j) :
    ∃ (B' : Set V) (ψ : V → (R →+* ℂ)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', a b = spMap (ψ b) ≫ j) ∧
      ∀ t : R, DifferentiableOn ℂ (fun b => ψ b t) B' := by
  classical
  let U : X.Opens := j ''ᵁ ⊤
  have hU : ∀ x : X, x ∈ U ↔ x ∈ Set.range j := fun x => by
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hl : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ U → ∃ ψ : R →+* ℂ, x = spMap ψ ≫ j := fun x hx => by
    have hr : Set.range x ⊆ Set.range j := by
      rintro _ ⟨q, rfl⟩
      exact (hU _).1 (hx (Set.mem_univ q))
    refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
    rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have h₀ : ⊤ ≤ a b₀ ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 ((hU _).2 hj)
  let ψ : V → (R →+* ℂ) := fun b => if hb : ⊤ ≤ a b ⁻¹ᵁ U then (hl _ hb).choose else (hl _ h₀).choose
  have hψ : ∀ b, ⊤ ≤ a b ⁻¹ᵁ U → a b = spMap (ψ b) ≫ j := fun b hb => by
    simp only [ψ, dif_pos hb]
    exact (hl _ hb).choose_spec
  refine ⟨{b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U}, ψ, (h U 0).1, ⟨hb₀, h₀⟩, fun b hb => hb.1, fun b hb => hψ b hb.2, fun t => ?_⟩
  refine (h U ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t))).2.congr fun b hb => ?_
  have hle : (⊤ : (Sp R).Opens) ≤ j ⁻¹ᵁ U := fun y _ => (hU _).2 ⟨y, rfl⟩
  have hid : (j.appIso ⊤).inv ≫ j.appLE U ⊤ hle = 𝟙 _ := by
    rw [Scheme.Hom.appIso_inv_appLE]
    exact (Sp R).presheaf.map_id _
  rw [hψ b hb.2, ← valAt'_appLE (spMap (ψ b)) j U ⊤ hle _ le_top, ← CommRingCat.comp_apply, hid]
  exact (valAt'_spMap (ψ b) t).symm

theorem exists_chart_holomorphic :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => _root_.Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b₀ ∈ T.co ⁻¹' (M.X k).dom, ∃ (p : TRing c.F) (y₀ : FrPt Xo c p.R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (p.R →ₐ[c.F] CAt σ)), IsOpen B ∧ b₀ ∈ B ∧ B ⊆ T.co ⁻¹' (M.X k).dom ∧ (∀ b ∈ B, F.u k (T.Pf (T.co b)) = spMap (ψ b).toRingHom ≫ y₀.x) ∧ ∀ t : p.R, DifferentiableOn ℂ (fun b => _root_.Formalism.L2.PjFree.toC (ψ b t)) B := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b₀ hb₀
  classical
  set D : Set (Fin T.m → ℂ) := T.co ⁻¹' (M.X k).dom with hD
  have hDo : IsOpen D := (FourierCoefficientDomain.isOpen_dom (M.X k)).preimage T.co.continuous
  have hu : IsHolTo D (fun b => F.u k (T.Pf (T.co b))) := (F.hol k T.m D _ hDo T.holPer).1
  have hw : ∀ b ∈ D, F.u k (T.Pf (T.co b)) ≫ Xo.s =
      spMap σ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := fun b hb => by
    rw [F.over_σ k _ (T.isPer _ hb), spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  let a : (Fin T.m → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ D then pullback.lift _ _ (hw b hb) else pullback.lift _ _ (hw b₀ hb₀)
  have ha₁ : ∀ b ∈ D, a b ≫ pullback.fst _ _ = F.u k (T.Pf (T.co b)) := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_fst]
  have ha₂ : ∀ b ∈ D, a b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    simp only [a, dif_pos hb, pullback.lift_snd]
  have ha : IsHolTo D a := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
    (isHolTo_congr hu ha₁) (isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hDo (spMap σ)) ha₂)
  obtain ⟨p, j, y₀, ⟨hj, hj₁, hj₂⟩, hz⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (a b₀ (default : PrimeSpectrum ℂ))
  obtain ⟨B, ψ, hBo, hb, hBD, hψ, hol⟩ := exists_coordinates ha j hb₀ hz
  have hc : ∀ b ∈ B, ∀ x, ψ b (algebraMap c.F p.R x) = σ x := fun b hb x => by
    have h₂ := ha₂ b (hBD hb)
    rw [hψ b hb, Category.assoc, hj₂, spMap, spMap, spMap, ← Spec.map_comp] at h₂
    exact congrArg (fun φ => φ.hom x) (Spec.map_injective h₂)
  let mk : ∀ b ∈ B, p.R →ₐ[c.F] CAt σ := fun b hb =>
    { toRingHom := (ψ b : p.R →+* CAt σ), commutes' := hc b hb }
  refine ⟨p, y₀, B, fun b => if h : b ∈ B then mk b h else mk b₀ hb, hBo, hb, hBD, fun b h => ?_, fun t => ?_⟩
  · simp only [dif_pos h]
    rw [← ha₁ b (hBD h), hψ b h, Category.assoc, hj₁]
    rfl
  · refine (hol t).congr fun b h => ?_
    simp only [dif_pos h]
    rfl

end GlobalTheory.HolChart
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.SecFieldCompare

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map
  map_cancel hasBC_of exists_testRing_ext)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionBaseChangeTests (IsBCTest SecBCTest SecBCAll)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def homRes {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T) : S →ₐ[c.F] T :=
  { ψ.toRingHom with
    commutes' := fun a => by
      show ψ (algebraMap c.F S a) = algebraMap c.F T a
      rw [← hS a, ψ.commutes, hT a] }

theorem frMap_res_iff {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (ψ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (homRes hle hS hT ψ) (y.res hle hS) (z.res hle hT) ↔ FrMap ψ y z := Iff.rfl

theorem fromT_of_res (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S]
    (h : AlgOver c c' hle S) (y : FrPt Xo c' S) (hy : FromT (y.res hle h)) : FromT y := by
  obtain ⟨p, φ, y₀, hy₀⟩ := hy
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  obtain ⟨q, α, hα, hlift, -⟩ := exists_testRing_ext (K' := c'.F) p
  obtain ⟨β, hβ⟩ := hlift S φ.toRingHom fun a => (φ.commutes a).trans (h a).symm
  let : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
  have hq : AlgOver c c' hle q.R := fun _ => rfl
  let α' : p.R →ₐ[c.F] q.R := { α with commutes' := hα }
  obtain ⟨y₁, hy₁⟩ := hBC _ _ α' y₀
  have e : (homRes hle hq h β).comp α' = φ := AlgHom.ext hβ
  have h₂ : FrMap (homRes hle hq h β) y₁ (y.res hle h) := map_cancel hBC e hy₁ hy₀
  exact ⟨q, β, y₁.ext hle hq, (frMap_res_iff hle hq h β (y₁.ext hle hq) y).1 h₂⟩

variable (Xo)

end GlobalTheory.SecFieldCompare
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem infiniteAdele_bijective : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  intro D
  have hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x) :=
    fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : cF D ≠ 1 := by
    intro h
    have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
    have h1 := hτ D.host.φ₀ D.host.sqrtMinusD
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    exact h0.2.2 (by linarith)
  have H := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ
  refine ⟨?_, fun θ hθ => ?_⟩
  · choose θ hθ using H.1
    exact ⟨θ, hθ⟩
  · obtain ⟨h1, h2, h3⟩ := H.2 θ hθ
    refine ⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩
    have := cm_type_mem_iff_conj_not_mem D τ
    rw [mem_cm_type_iff, mem_cm_type_iff] at this
    exact this

end GlobalTheory.Member
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem sab_extensions_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp K ⟶ Xo.X) (G G₂ : SAB H (Sp T)) (t t₂ : SAB H (Sp K)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T K))) (n₁ : SABMap t₂ Xo.univ.t x) (n₂ : SABMap t₂ G₂ (spMap (algebraMap T K))), ∃ (k : SABMap t t₂ (𝟙 _)) (n : SABMap G G₂ (𝟙 _)), k.φ ≫ n₁.φ = m₁.φ ∧ m₂.φ ≫ n.φ = k.φ ≫ n₂.φ := by
  intro E _ _ _ H Dw l Xo T K _ _ _ _ _ _ x G G₂ t t₂ m₁ m₂ n₁ n₂
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m₁', hm₁⟩ := tr (Category.id_comp x).symm m₁
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ x (𝟙 _) n₁ m₁'
  obtain ⟨c, hc⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ (𝟙 _) n₂ k
  obtain ⟨c', hc'⟩ := tr (Category.id_comp _) c
  obtain ⟨ψ, hψ, hφ, hact⟩ := sab_group_iso_of_generic
    (existsUnique_hom_extension_semiAbelian_dvr (AbelianSubgroupFinite.finite_of_no_torsion abMulN_holds))
    E H T K G G₂ t m₂ c'
  obtain ⟨n, hn⟩ := Exist.CubicalExtension.sabMap_of_iso_of_extendGen
    (cubical_extends_and_extendGen forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
      GenExtend.existsUnique_gen_extend).2 E H T K G G₂ t m₂ c' ψ hψ hφ hact
  exact ⟨k, n, by rw [← hk, hm₁], by rw [hn, hφ, hc', hc]⟩

end GlobalTheory
end
