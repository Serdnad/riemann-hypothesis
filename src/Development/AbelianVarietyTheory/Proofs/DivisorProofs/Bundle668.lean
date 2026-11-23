module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle629
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle623
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.Analysis.Complex.Circle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupCharacterEqOneOfTrivialIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

theorem eigSp_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  intro F _ _ g φ s τ hτ
  let ρ : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).toRingEquiv.toRingHom.comp φ
  have hcomm : ∀ a b : 𝓞 F, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : 𝓞 F => ρ a)
    (fun i j m => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) m)
  let χ : (F →+* ℂ) → (𝓞 F → ℂ) := fun σ c => σ (c : F)
  have hχ : Function.Injective χ := by
    intro σ₁ σ₂ he
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact congrFun he c
  have hle : ∀ σ : F →+* ℂ, eigSp φ σ ≤ ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (χ σ c) := by
    intro σ u hu
    rw [Submodule.mem_iInf]
    intro c
    apply (Module.End.genEigenspace (ρ c) (χ σ c)).mono le_top
    rw [Module.End.mem_eigenspace_iff]
    have := hu c
    simpa [ρ, χ, Matrix.toLin'_apply] using this
  have hnot : χ τ ∉ (χ '' (s : Set (F →+* ℂ))) := by
    rintro ⟨σ, hσ, he⟩
    exact hτ (hχ he ▸ hσ)
  have hd := h.disjoint_biSup hnot
  refine (hd.mono_left (hle τ)).mono_right ?_
  refine iSup₂_le fun σ hσ => (hle σ).trans ?_
  exact le_iSup₂_of_le (f := fun (x : 𝓞 F → ℂ) (_ : x ∈ χ '' (s : Set (F →+* ℂ))) => ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (x c)) (χ σ) ⟨σ, hσ, rfl⟩ le_rfl

end GlobalTheory.UPel.HT.LieType
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
open scoped NNReal ENNReal

noncomputable section

attribute [local instance 2000] GlobalTheory.SplitWeil.matrixMeasurableSpace

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

def StdSupp (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : Prop :=
  (∀ i j, x.toRows₁ i j ∈ 𝒪[k]) ∧ valuation k x.toRows₁.det = 1 ∧ ∀ i j, x.toRows₂ i j ∈ cball (ϖ ^ c)

theorem StdSupp.det_ne {ϖ : kˣ} {c : ℕ} {x : Matrix (Fin n ⊕ Fin n') (Fin n) k} (h : StdSupp ϖ c x) :
    x.toRows₁.det ≠ 0 := fun h0 => by
  have := h.2.1
  rw [h0, map_zero] at this
  exact zero_ne_one this


open Classical in
def stdDatum (μ : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (x : Matrix (Fin n ⊕ Fin n') (Fin n) k) : ℂ :=
  if h : StdSupp ϖ c x then (((μ (Units.mk0 _ h.det_ne))⁻¹ : ℂˣ) : ℂ) else 0

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta

namespace GlobalTheory.StdLocZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : ℕ}

end GlobalTheory.StdLocZeta
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section
namespace GlobalTheory.LevCover

theorem implocus_open_closed : ∀ (Y : Scheme.{0}) (Z : Over Y) (P Q : ∀ T : Over Y, (T ⟶ Z) → Prop), IsFinite Z.hom → Etale Z.hom → GlobalTheory.LevCover.ClopenCond Z P → GlobalTheory.LevCover.ClopenCond Z Q → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔ ∀ z : Over.mk x ⟶ Z, P _ z → Q _ z := by
  intro Y Z P Q hfin het hP hQ
  obtain ⟨U, hUc, HU⟩ := hP
  obtain ⟨V, hVc, HV⟩ := hQ
  let B : Set Z.left := (U : Set Z.left) \ V
  have hBo : IsOpen B := U.isOpen.sdiff hVc
  have hBc : IsClosed B := hUc.sdiff V.isOpen
  have c1 : ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ (Z.hom.base '' B)ᶜ ↔
      ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ z : T ⟶ Z, P T z → Q T z := by
    intro Tb t
    constructor
    · intro hW T σ hσ z hPz
      rw [HU] at hPz
      rw [HV]
      rintro _ ⟨w, rfl⟩
      by_contra hv
      have hb : z.left.base w ∈ B := ⟨hPz ⟨w, rfl⟩, hv⟩
      apply hW ⟨σ.base w, rfl⟩
      refine ⟨_, hb, ?_⟩
      rw [← Scheme.Hom.comp_apply, Over.w z, ← hσ, Scheme.Hom.comp_apply]
    · intro H
      rintro _ ⟨τ, rfl⟩ ⟨u, hu, hτ⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback τ u hτ.symm
      let O : (pullback t Z.hom).Opens := (pullback.snd t Z.hom) ⁻¹ᵁ ⟨B, hBo⟩
      let T : Over Y := Over.mk (O.ι ≫ pullback.fst t Z.hom ≫ t)
      let z : T ⟶ Z := Over.homMk (O.ι ≫ pullback.snd t Z.hom) (by simp [T, pullback.condition])
      have hmem : ∀ w, O.ι.base w ∈ (O : Set _) := fun w => by
        rw [← Scheme.Opens.range_ι O]; exact ⟨w, rfl⟩
      have hPz : P T z := by
        rw [HU]
        rintro _ ⟨w, rfl⟩
        exact (hmem w).1
      have hQz := H T (O.ι ≫ pullback.fst t Z.hom) (Category.assoc _ _ _) z hPz
      rw [HV] at hQz
      have hpO : p ∈ Set.range O.ι.base := by
        rw [Scheme.Opens.range_ι O]
        show (pullback.snd t Z.hom).base p ∈ B
        rw [hp2]; exact hu
      obtain ⟨w, hw⟩ := hpO
      apply hu.2
      have := hQz ⟨w, rfl⟩
      simpa [z, Scheme.Hom.comp_apply, hw, hp2] using this
  refine ⟨(Z.hom.base '' B)ᶜ, (Z.hom.isClosedMap _ hBc).isOpen_compl,
    (Z.hom.isOpenMap _ hBo).isClosed_compl, c1, ?_⟩
  intro k _ _ x
  constructor
  · intro hW z hPz
    exact (c1 (Sp k) x).1 hW (Over.mk x) (𝟙 _) (Category.id_comp _) z hPz
  · intro H
    rintro _ ⟨s, rfl⟩ ⟨u, hu, hs⟩
    let Bo : Z.left.Opens := ⟨B, hBo⟩
    haveI : IsClosedImmersion Bo.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hBc)
    have huB : u ∈ Set.range Bo.ι.base := by rw [Scheme.Opens.range_ι]; exact hu
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := GlobalTheory.LevCover.exists_lift_geom (Bo.ι ≫ Z.hom) x (by
      rintro _ ⟨s', rfl⟩
      refine ⟨v, ?_⟩
      rw [Subsingleton.elim s' s, Scheme.Hom.comp_apply, hv, hs])
    let z : Over.mk x ⟶ Z := Over.homMk (w ≫ Bo.ι) (by simpa using hw)
    have hPz : P _ z := by
      rw [HU]
      rintro _ ⟨y, rfl⟩
      have : (Bo.ι.base (w.base y)) ∈ (Bo : Set Z.left) := by
        rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
      exact this.1
    have hQz := H z hPz
    rw [HV] at hQz
    let y0 : Sp k := (⊥ : PrimeSpectrum k)
    have h1 : (Bo.ι.base (w.base y0)) ∈ (Bo : Set Z.left) := by
      rw [← Scheme.Opens.range_ι Bo]; exact ⟨_, rfl⟩
    exact h1.2 (hQz ⟨y0, rfl⟩)

end GlobalTheory.LevCover
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}), ∃ (b : A) (z : A ⊗[O] A), cobOne O A b = a • z ∧ ∀ φ : CartierDual O A, u (dUnit (R := O) φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.cartierDual_tangent_mod | exact GlobalTheory.cartierDual_tangent_mod | (intros; apply GlobalTheory.cartierDual_tangent_mod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTorsRep

theorem absNorm_coprime {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] (𝔟 : Ideal (𝓞 K))
    (h : 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} = ⊤) : (Ideal.absNorm 𝔟).Coprime p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  have h1 : (1 : 𝓞 K) ∈ 𝔟 ⊔ Ideal.span {(p : 𝓞 K)} := h ▸ Submodule.mem_top
  obtain ⟨β, hβ, z, hz, hβz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  by_cases h0 : 𝔟 = ⊥
  · subst h0
    have hβ0 : β = 0 := (Submodule.mem_bot _).1 hβ
    subst hβ0
    rw [zero_add] at hβz
    have hu : IsUnit (p : 𝓞 K) := ⟨⟨(p : 𝓞 K), y, by rw [mul_comm]; exact hβz, hβz⟩, rfl⟩
    have hu' := hu.map (Algebra.norm ℤ : 𝓞 K →* ℤ)
    rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at hu'
    have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := (Module.finrank_pos).ne'
    rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu'
    rcases hu' with h' | h'
    · exact hp.out.one_lt.ne' (by exact_mod_cast h')
    · have : (0 : ℤ) ≤ p := by positivity
      omega
  · have hne : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hne hdvd
    have : Finite (𝓞 K ⧸ 𝔟) := Nat.finite_of_card_ne_zero hne
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hdvd
    have hpx : (p : 𝓞 K ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have h1' : (Ideal.Quotient.mk 𝔟 y) * (p : 𝓞 K ⧸ 𝔟) = 1 := by
      have := congrArg (Ideal.Quotient.mk 𝔟) hβz
      rwa [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hβ, zero_add, map_mul, map_natCast, map_one] at this
    have hx0 : x = 0 := by
      rw [← _root_.one_mul x, ← h1', _root_.mul_assoc, hpx, MulZeroClass.mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.out.one_lt.ne hx

section Tors

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (n : ℕ)

theorem mono_of_unit {X : Over S} (e : 𝟙_ (Over S) ⟶ X) : Mono e := ⟨fun g h _ => toUnit_unique g h⟩

theorem ι_mulN : torsion.ι A n ≫ mulN A n = toUnit _ ≫ η[A] := by
  exact (pullback.condition (f := mulN A n) (g := (η : 𝟙_ (Over S) ⟶ A))).trans
    (congrArg (· ≫ η[A]) (toUnit_unique _ _))

def torsEta : 𝟙_ (Over S) ⟶ torsion A n :=
  pullback.lift η[A] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

theorem mono_ι : Mono (torsion.ι A n) := by
  have := mono_of_unit η[A]
  exact pullback.fst_of_mono

def torsAct (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) : torsion A n ⟶ torsion A n :=
  pullback.lift (torsion.ι A n ≫ f) (toUnit _) (by
    rw [Category.assoc, hf, ← Category.assoc, ι_mulN, Category.assoc, IsMonHom.one_hom])

@[simp]
theorem torsAct_ι (f : A ⟶ A) [IsMonHom f] (hf : f ≫ mulN A n = mulN A n ≫ f) :
    torsAct n f hf ≫ torsion.ι A n = torsion.ι A n ≫ f := pullback.lift_fst _ _ _

theorem exists_openClosed {Ix : Type} [DecidableEq Ix] (act : Ix → (A ⟶ A)) [∀ a, IsMonHom (act a)]
    (hc : ∀ a, act a ≫ mulN A n = mulN A n ≫ act a) [Etale (torsion A n).hom] [IsSeparated (torsion A n).hom]
    (t : Finset Ix) :
    ∃ (Z : Over S) (j : Z ⟶ torsion A n), Mono j ∧ IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (W : Over S) (y : W ⟶ torsion A n), (∃ z, z ≫ j = y) ↔ ∀ a ∈ t, y ≫ torsion.ι A n ≫ act a = 1 := by
  have hEta : torsEta n ≫ torsion.ι A n = η[A] := pullback.lift_fst _ _ _
  have hsec : IsOpenImmersion (torsEta (A := A) n).left ∧ IsClosedImmersion (torsEta (A := A) n).left :=
    GlobalTheory.isOpenImmersion_and_isClosedImmersion_of_section_of_etale (torsion A n).hom _ (Over.w (torsEta n))
  have := hsec.1; have := hsec.2
  have := mono_of_unit (torsEta (A := A) n)
  have := mono_ι (A := A) n
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨_, 𝟙 _, inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance, fun W y =>
      ⟨fun _ a ha => absurd ha (Finset.notMem_empty a), fun _ => ⟨y, Category.comp_id y⟩⟩⟩
  | insert a t hat ih =>
    obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := ih
    let g := j ≫ torsAct n (act a) (hc a)
    have hP := (IsPullback.of_hasPullback g (torsEta n)).map (Over.forget S)
    have ho : IsOpenImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip hsec.1
    have hcl : IsClosedImmersion (pullback.fst g (torsEta n)).left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hP.flip hsec.2
    refine ⟨pullback g (torsEta n), pullback.fst g (torsEta n) ≫ j, inferInstance, ?_, ?_, fun W y => ?_⟩
    · rw [Over.comp_left]; infer_instance
    · rw [Over.comp_left]; infer_instance
    constructor
    · rintro ⟨z, rfl⟩ b hb
      rcases Finset.mem_insert.1 hb with rfl | hb
      · have e : j ≫ torsion.ι A n ≫ act b = g ≫ torsion.ι A n := by simp [g]
        simp only [Category.assoc]
        rw [e, ← Category.assoc (pullback.fst g _), pullback.condition]
        simp only [Category.assoc, hEta]
        rw [← Category.assoc, toUnit_unique (z ≫ pullback.snd g (torsEta n)) (toUnit W)]; rfl
      · exact (hpts W _).1 ⟨z ≫ pullback.fst _ _, Category.assoc _ _ _⟩ b hb
    · intro h
      obtain ⟨w, hw⟩ := (hpts W y).2 (fun b hb => h b (Finset.mem_insert_of_mem hb))
      have hwg : w ≫ g = toUnit W ≫ torsEta n := by
        rw [← cancel_mono (torsion.ι A n)]
        simp only [g, Category.assoc, torsAct_ι, hEta]
        rw [← Category.assoc w j, hw, h a (Finset.mem_insert_self a t)]; rfl
      exact ⟨pullback.lift w (toUnit W) hwg, by rw [← Category.assoc, pullback.lift_fst, hw]⟩

end Tors


open GlobalTheory.IwLevel in
theorem exists_finiteEtale_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∃ (K : Over S) (i : K ⟶ o.A), Mono i ∧ IsFinite K.hom ∧ Etale K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N S s o 𝔟 h𝔟
  classical
  set n := Ideal.absNorm 𝔟 with hn_def
  have hcop := absNorm_coprime p 𝔟 h𝔟
  have hnR : IsUnit ((n : ℕ) : R) := b.unit n hcop
  have hnS : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
    have := hnR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hnS
  have hactN : ∀ k : ℕ, o.act.act (k : D.O) = mulN o.A k := by
    intro k
    induction k with
    | zero =>
      have h := o.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero]
      exact left_eq_mul.1 h
    | succ k ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one]; rfl
  have hc : ∀ a : D.O, o.act.act a ≫ mulN o.A n = mulN o.A n ≫ o.act.act a := by
    intro a
    rw [← hactN, ← o.act.mul, ← o.act.mul, Nat.cast_comm]
  haveI : ∀ a, IsMonHom (o.act.act a) := o.act.hom
  haveI : IsSeparated (torsion o.A n).hom := inferInstance
  have : Module.Finite ℤ D.O := D.finO
  have : IsNoetherian D.O D.O := isNoetherian_of_tower ℤ inferInstance
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (𝔟.map (algebraMap (𝓞 D.F) D.O))
  obtain ⟨Z, j, hj, hjo, hjc, hpts⟩ := exists_openClosed n o.act.act hc t
  have := mono_ι (A := o.A) n
  refine ⟨Z, j ≫ torsion.ι o.A n, inferInstance, ?_, ?_, fun T x => ?_⟩
  · rw [← Over.w j]; infer_instance
  · rw [← Over.w j]; infer_instance
  rw [← ht]
  refine Iff.trans ?_ (killedBy_span (htAct o) (t : Set D.O) x).symm
  simp only [htAct_act]
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simpa only [Category.assoc] using (hpts T (z ≫ j)).1 ⟨z, rfl⟩ a ha
  · intro hx
    have hn𝔟 : ((n : ℕ) : 𝓞 D.F) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
    have hnO : ((n : ℕ) : D.O) ∈ Submodule.span D.O (t : Set D.O) := by
      rw [ht]; simpa using Ideal.mem_map_of_mem (algebraMap (𝓞 D.F) D.O) hn𝔟
    have hxn : x ≫ mulN o.A n = toUnit T ≫ η[o.A] := by
      rw [← hactN]
      have := (killedBy_span (htAct o) (t : Set D.O) x).2 (by simpa only [htAct_act] using hx) _ hnO
      exact this
    let y : T ⟶ torsion o.A n := pullback.lift x (toUnit T) hxn
    have hy : y ≫ torsion.ι o.A n = x := pullback.lift_fst _ _ _
    obtain ⟨z, hz⟩ := (hpts T y).2 (fun a ha => by rw [← Category.assoc, hy]; exact hx a ha)
    exact ⟨z, by rw [← Category.assoc, hz, hy]⟩

end GlobalTheory.HTTorsRep
end
end

section

open NumberField

namespace GlobalTheory.MaximalIdealDividingNorm

theorem exists_maximal_above_of_dvd_norm {K : Type*} [Field K] [NumberField K]
    (𝔪 : Ideal (𝓞 K)) {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 K) ∈ P := by
  obtain ⟨P, hmax, hunder, hdiv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔪 hd
  refine ⟨P, hmax, Ideal.le_of_dvd hdiv, ?_⟩
  have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
    rw [hunder]
    exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := Ideal.mem_comap.mp h1
  rwa [map_natCast] at h2

theorem exists_maximal_above_of_dvd_norm_host (D : Formalism.BasicNotions.D7)
    (𝔪 : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E)) (_h𝔪 : 𝔪 ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm 𝔪) :
    ∃ P : Ideal (𝓞 (Formalism.BasicNotions.D7.host D).E),
      P.IsMaximal ∧ 𝔪 ≤ P ∧ (p : 𝓞 (Formalism.BasicNotions.D7.host D).E) ∈ P :=
  exists_maximal_above_of_dvd_norm 𝔪 hp hd

end GlobalTheory.MaximalIdealDividingNorm
end

section

open Formalism.UG

theorem _root_.GlobalTheory.T.unitaryGroup_character_eq_one_of_trivial_integral : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle, (∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.UnitaryCharacter.char_eq_one | exact GlobalTheory.UnitaryCharacter.char_eq_one | (intros; apply GlobalTheory.UnitaryCharacter.char_eq_one <;> assumption)
end
