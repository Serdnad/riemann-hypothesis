module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle006
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle029
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle099
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
import Formalism.CyclotomicNorms.Bundle001
import Formalism.LocalToGlobal.Divisibility.Bundle001
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

end
end

section

noncomputable section

namespace GlobalTheory.GoodFamily

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.BI GlobalTheory.GoodCharsCompare Formalism.MainNotions.PrimeDegreeVariant
open scoped MonoidAlgebra

section Characters

theorem irreducible_of_surjective {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [Nontrivial V]
    (ρ : Representation k G V) (h : Function.Surjective ρ.asAlgebraHom) : ρ.IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun w _ => ?_))
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
    obtain ⟨a, ha⟩ := h (LinearMap.smulRight φ w)
    have hw : ρ.asAlgebraHom a v = w := by rw [ha]; simp [hφ]
    rw [← hw]
    clear hw ha
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact S.toSubmodule.add_mem hx hy
    | single t c =>
      rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
      exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule t hv)

theorem irreducible_extend (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] {G : Type} [Group G]
    [Finite G] {n : ℕ} (ρ : Representation K G (Fin n → K))
    (h : Module.finrank K (Representation.IntertwiningMap ρ ρ) = 1) : (extendScalarsRep K L ρ).IsIrreducible := by
  have h1 := pair_character_eq_finrank K L G _ _ ρ ρ
  have h2 := pair_character_eq_finrank L L G _ _ (extendScalarsRep K L ρ) (extendScalarsRep K L ρ)
  simp only [character_extendScalarsRep, Algebra.algebraMap_self, RingHom.id_apply] at h2
  rw [h1, h] at h2
  obtain ⟨h3, h4⟩ := GlobalTheory.asAlgebraHom_surjective_of_finrank_intertwiningMap_eq_one L G _ (extendScalarsRep K L ρ)
    (by exact_mod_cast h2.symm)
  exact irreducible_of_surjective _ h4

theorem norm_one_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)] {χ : ∀ i, G i → ℂ}
    (h : ∀ i, IsChar ℂ ℂ (χ i) ∧ pair (χ i) (χ i) = 1) :
    IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i, χ i (t i)) ∧
      pair (fun t : ∀ i, G i => ∏ i, χ i (t i)) (fun t => ∏ i, χ i (t i)) = 1 := by
  classical
  constructor
  · have : ∀ s : Finset ι, IsChar ℂ ℂ (fun t : ∀ i, G i => ∏ i ∈ s, χ i (t i)) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using isChar_one ℂ ℂ (∀ i, G i)
      | insert a s ha ih =>
        obtain ⟨n, ρ, hρ⟩ := (h a).1
        have h1 : IsChar ℂ ℂ (fun t : ∀ i, G i => χ a (t a)) := ⟨n, ρ.comp (Pi.evalMonoidHom G a), fun t => hρ (t a)⟩
        have := isChar_mul_complex h1 ih
        convert this using 1
        funext t
        rw [Finset.prod_insert ha]; rfl
    exact this _
  · letI : ∀ i, Fintype (G i) := fun i => Fintype.ofFinite _
    have h2 : ∏ i, pair (χ i) (χ i) = 1 := Finset.prod_eq_one fun i _ => (h i).2
    rw [← h2]
    simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib, Pi.inv_apply]

end Characters

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {g : ℕ} [Fact g.Prime] {r : ℕ}

end Local

section Global

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

end Global

end GlobalTheory.GoodFamily
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem blkMat_one_mem (hr : r ≤ a) (k : Kinf E (a - r)) :
    blkMat (Cinf E) hr (1, k.1) ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have hs : star (blkMat (Cinf E) hr (1, k.1)) = blkMat (Cinf E) hr (1, star k.1) := by
    change Matrix.conjTranspose (Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 k.1)) =
      Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 (Matrix.conjTranspose k.1))
    rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]
    simp
  rw [Matrix.mem_unitaryGroup_iff', hs, ← map_mul]
  have : ((1 : Matrix (Fin r) (Fin r) (Cinf E)), star k.1) * (1, k.1) = 1 :=
    Prod.ext (mul_one _) (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [this, map_one]

def blkK (hr : r ≤ a) (k : Kinf E (a - r)) : Kinf E a := ⟨blkMat (Cinf E) hr (1, k.1), blkMat_one_mem hr k⟩

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem toUnits_blkK (hr : r ≤ a) (k : Kinf E (a - r)) :
    Unitary.toUnits (blkK hr k) = blkGL hr (1, Unitary.toUnits k) := Units.ext rfl


variable (E) in
def slice [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) : GA E (a - r) → ℂ :=
  fun m₂ => ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ

def levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))) :
    Subgroup (GL (Fin (a - r)) (Af E)) :=
  (L.map (MulAut.conj t).toMonoidHom).comap ((blkGL hr).comp (MonoidHom.inr _ _))

theorem mem_levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E)))
    (l : GL (Fin (a - r)) (Af E)) : l ∈ levelSub hr t L ↔ t⁻¹ * blkGL hr (1, l) * t ∈ L := by
  simp only [levelSub, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by group⟩

def ktypeSub (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Kinf E (a - r) → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ fun k => κ⁻¹ * blkK hr k * κ)

instance (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (ktypeSub hr κ W) := by
  unfold ktypeSub; infer_instance

theorem blkGL_one_corner {R S : Type} [CommRing R] [CommRing S] (hr : r ≤ a) (s : R →ₙ+* S)
    (l : GL (Fin (a - r)) R) : blkGL hr (1, cornerGL (a - r) s l) = cornerGL a s (blkGL hr (1, l)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  change _ = (1 : Matrix (Fin a) (Fin a) S) _ _ - s ((1 : Matrix (Fin a) (Fin a) R) _ _) + s ((blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) _ _)
  rw [blkGL_apply]
  have e1 : ∀ {T : Type} [CommRing T] (i j : Fin r ⊕ Fin (a - r)),
      (1 : Matrix (Fin a) (Fin a) T) (blkEquiv hr i) (blkEquiv hr j) = (1 : Matrix (Fin r ⊕ Fin (a - r)) _ T) i j := by
    intro T _ i j
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1, e1]
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.one_apply]
  · simp
  · simp
  · change (1 : Matrix _ _ S) i j - s ((1 : Matrix _ _ R) i j) + s (l i j) = _
    simp [Matrix.one_apply]

theorem blkGL_mul_finGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (l : GL (Fin (a - r)) (Af E)) :
    blkGL hr (m₁, m₂ * finGL E (a - r) l) = blkGL hr (m₁, m₂) * finGL E a (blkGL hr (1, l)) := by
  rw [show (m₁, m₂ * finGL E (a - r) l) = (m₁, m₂) * (1, finGL E (a - r) l) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ l)

theorem blkGL_mul_infGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (y : GL (Fin (a - r)) (Cinf E)) :
    blkGL hr (m₁, m₂ * infGL E (a - r) y) = blkGL hr (m₁, m₂) * infGL E a (blkGL hr (1, y)) := by
  rw [show (m₁, m₂ * infGL E (a - r) y) = (m₁, m₂) * (1, infGL E (a - r) y) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ y)

theorem slice_mul_finGL [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (L : Subgroup (GL (Fin a) (Af E)))
    (hφ : ∀ k ∈ L, ∀ g, φ (g * finGL E a k) = φ g) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (l : GL (Fin (a - r)) (Af E)) (hl : l ∈ levelSub hr t L) (g : GA E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * finGL E (a - r) l) = slice E μ 𝓕 hr φ m₁ t κ g := by
  unfold slice
  congr 1
  funext x
  have hk := hφ _ ((mem_levelSub hr t L l).1 hl)
    (unip x * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
  rw [← hk, blkGL_mul_finGL]
  congr 1
  have e : finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t) = finGL E a (blkGL hr (1, l)) * finGL E a t := by
    rw [← map_mul, ← map_mul]; congr 1; group
  calc unip x * (blkGL hr (m₁, g) * finGL E a (blkGL hr (1, l)) * finGL E a t * infGL E a (Unitary.toUnits κ))
      = unip x * (blkGL hr (m₁, g) * (finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t)) *
          infGL E a (Unitary.toUnits κ)) := by rw [e]; simp only [mul_assoc]
    _ = unip x * (blkGL hr (m₁, g) * finGL E a t * (infGL E a (Unitary.toUnits κ) *
          finGL E a (t⁻¹ * blkGL hr (1, l) * t))) := by rw [infGL_comm]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem slice_mul_cpt [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) (g : GA E (a - r)) (k : Kinf E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k)) =
      ∫ x in 𝓕, φ (unip x * ((blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)) *
        infGL E a (Unitary.toUnits (κ⁻¹ * blkK hr k * κ)))) ∂μ := by
  unfold slice
  congr 1
  funext x
  congr 2
  rw [blkGL_mul_infGL]
  simp only [map_mul, map_inv, toUnits_blkK]
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (infGL E a (blkGL hr (1, Unitary.toUnits k))) (finGL E a t),
    infGL_comm (blkGL hr (1, Unitary.toUnits k)) t]
  simp only [mul_assoc]

end GlobalTheory.SliceTwo

end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_noetherian_model_torsor_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j →
    ∀ (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T), Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
      ∃ (DA : Type) (_ : CommRing DA) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)
        (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA ∧
        ∀ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA →
          ∃ σ₁ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_noetherian_model) | (exact GlobalTheory.KeyOriginNoeth.exists_noetherian_model) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_noetherian_model  <;> assumption)
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_section_strictHenselisation_closedFibre_point : GlobalTheory.LocAcyc.KeyClosedPts →
    ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
      [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (y : Ideal E) [y.IsPrime],
      (y.comap (algebraMap (Polynomial T) E)).comap (Polynomial.C : T →+* Polynomial T) =
        IsLocalRing.maximalIdeal T →
      y.comap (algebraMap (Polynomial T) E) ≠
        (IsLocalRing.maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (DE : Type) [CommRing DE] [Algebra (GlobalTheory.LocAcyc.GenFib T E) DE]
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE →
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ s : DE →+* GlobalTheory.LocAcyc.GenFib T S,
        ∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap S (GlobalTheory.LocAcyc.GenFib T S) (algebraMap E S e) := by
  first | exact @GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | exact GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed | (intros; apply GlobalTheory.LocAcyc.exists_section_strictHenselisation_at_closed <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := GlobalTheory.T.jacobianDet_isFrameOn_canonicalWeight n Y ι La A U z hz
  have hW := GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.cechNonvanishing_lineBundleInvMix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB → ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_one_zero | exact GlobalTheory.AmpleGen.nv_mix_one_zero | (intros; apply GlobalTheory.AmpleGen.nv_mix_one_zero <;> assumption)
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

theorem _root_.GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  first | exact @GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | exact GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | (intros; apply GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed <;> assumption)
end

section

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

theorem _root_.GlobalTheory.T.leviPiTensorRepresentation_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  first | exact @GlobalTheory.HcIrr.leviTensor_isIrreducible | exact GlobalTheory.HcIrr.leviTensor_isIrreducible | (intros; apply GlobalTheory.HcIrr.leviTensor_isIrreducible <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.map_formalGroupLawQuasiLogarithms : ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p] (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ) (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ, MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧ (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧ (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t → Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  first | exact @GlobalTheory.Katz.quasiLog_map | exact GlobalTheory.Katz.quasiLog_map | (intros; apply GlobalTheory.Katz.quasiLog_map <;> assumption)
end

section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.leviWhittakerColumnCharacter_eigen_vecMul_ne_bot : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F) (h : blockTri (κ := F) b), (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) → eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ → eig σ (colSet F b k.val) (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | exact GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot <;> assumption)
end

section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
end
