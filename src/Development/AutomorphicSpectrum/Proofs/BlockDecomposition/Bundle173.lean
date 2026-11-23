module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Mathlib.RingTheory.Flat.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle157
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle159
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle160
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle128
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle161
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle162
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CosieveRel

universe w w'

theorem tens_transfer {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₂ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₂ i)] [∀ i, Module R (M₂ i)] {M' M₂' : Type w'} [AddCommGroup M'] [AddCommGroup M₂']
    {f : ∀ i, N i → M i → M'} {f₂ : ∀ i, N i → M₂ i → M₂'} (a : ∀ i, M i ≃ₗ[R] M₂ i) (a' : M' ≃+ M₂')
    (hc : ∀ i n x, a' (f i n x) = f₂ i n (a i x)) (ht : Tens R f) : Tens R f₂ := by
  obtain ⟨g, hg⟩ := ht
  let b : (∀ i, N i ⊗[R] M₂ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (a i).symm).toAddEquiv
  refine ⟨(b.trans g).trans a', fun i n x => ?_⟩
  have hb : b (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (a i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [b]
    · simp [b, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply, hb, hg, hc, LinearEquiv.apply_symm_apply]

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem pull_pull_id {D : Type 1} [Category.{0} D] {F : C ⥤ ModuleCat.{0} R} {E : D ⥤ ModuleCat.{0} R}
    (m : CH.Mor F E (RingHom.id R)) (m' : CH.Mor E F (RingHom.id R)) (j : ℕ)
    (h : ∀ f, m'.pullC j (m.pullC j f) = f) (x : CH.H F j) : m'.pull j (m.pull j x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

abbrev inn (U P : ObjectProperty C) : ObjectProperty U.FullSubcategory := fun T => P T.obj

abbrev toDirect (U P : ObjectProperty C) : (inn U P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((inn U P).ι ⋙ U.ι) fun T => T.property

abbrev ofDirect {U P : ObjectProperty C} (h : P ≤ U) : P.FullSubcategory ⥤ (inn U P).FullSubcategory :=
  (inn U P).lift (U.lift P.ι fun T => h _ T.property) fun T => T.property

def dirMor (F : C ⥤ ModuleCat.{0} R) (U P : ObjectProperty C) :
    CH.Mor (P.ι ⋙ F) ((inn U P).ι ⋙ U.ι ⋙ F) (RingHom.id R) where
  G := toDirect U P
  τ _ := LinearMap.id
  nat _ _ := rfl

def itMor (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) :
    CH.Mor ((inn U P).ι ⋙ U.ι ⋙ F) (P.ι ⋙ F) (RingHom.id R) where
  G := ofDirect h
  τ _ := LinearMap.id
  nat _ _ := rfl

def isoH (F : C ⥤ ModuleCat.{0} R) {U P : ObjectProperty C} (h : P ≤ U) (j : ℕ) :
    HU F P j ≃ₗ[R] HU (U.ι ⋙ F) (inn U P) j :=
  LinearEquiv.ofLinear ((dirMor F U P).pull j) ((itMor F h).pull j)
    (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl)) (LinearMap.ext (pull_pull_id _ _ j fun _ => rfl))

theorem isoH_morU {R' : Type} [CommRing R'] {σ : R →+* R'} {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} (m : CH.Mor F F' σ) {U P : ObjectProperty C}
    {U' P' : ObjectProperty C'} (hU : ∀ T, U' T → U (m.G.obj T)) (hP : ∀ T, P' T → P (m.G.obj T))
    (h : P ≤ U) (h' : P' ≤ U') (j : ℕ) (x : HU F P j) :
    isoH F' h' j ((morU m hP).pull j x) =
      (morU (morU m hU) (U := inn U P) (U' := inn U' P') fun T hT => hP _ hT).pull j (isoH F h j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem base_change_rel : ∀ {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    (G : C' ⥤ C) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Flat R (N i)] (F : ι → (C ⥤ ModuleCat.{0} R)) (F' : C' ⥤ ModuleCat.{0} R')
    (τ : ∀ i, N i → ∀ T : C', (F i).obj (G.obj T) →ₛₗ[σ] F'.obj T) (hτ : ∀ i n {T T' : C'} (φ : T ⟶ T') x,
      τ i n T' (((F i).map (G.map φ)).hom x) = (F'.map φ).hom (τ i n T x))
    (hadd : ∀ i n n' T x, τ i (n + n') T x = τ i n T x + τ i n' T x) (hsm : ∀ i (r : R) n T x, τ i (r • n) T x = σ r • τ i n T x)
    {A : Type} [Fintype A] (W : A → ObjectProperty C) (W' : A → ObjectProperty C')
    (hW : ∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T')
    (hW' : ∀ α ⦃T T' : C'⦄, (T ⟶ T') → W' α T → (∃ β, W' β T') → W' α T') (h : ∀ α T, W' α T → W α (G.obj T)),
    (∀ S : Finset A, S.Nonempty → ∀ j, Tens R (N := N) (M := fun i => HU (F i) (capS W S) j) (M' := HU F' (capS W' S) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := capS W S) (U' := capS W' S)
        fun T hT α hα => h α T (hT α hα)).pull j x) →
    ∀ j, Tens R (N := N) (M := fun i => HU (F i) (fun T => ∃ α, W α T) j) (M' := HU F' (fun T => ∃ α, W' α T) j)
      fun i n x => (morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) (U := fun T => ∃ α, W α T) (U' := fun T => ∃ α, W' α T)
        fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩).pull j x := by
  intro R R' _ _ σ C C' _ _ G ι _ _ N _ _ _ F F' τ hτ hadd hsm A _ W W' hW hW' h hyp j
  let U : ObjectProperty C := fun T => ∃ α, W α T
  let U' : ObjectProperty C' := fun T => ∃ α, W' α T
  have hUU : ∀ T, U' T → U (G.obj T) := fun T ⟨α, hα⟩ => ⟨α, h α T hα⟩
  let G₁ : U'.FullSubcategory ⥤ U.FullSubcategory := U.lift (U'.ι ⋙ G) fun T => hUU _ T.property
  refine GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (C := U.FullSubcategory) (C' := U'.FullSubcategory) G₁ N
    (fun i => U.ι ⋙ F i) (U'.ι ⋙ F') (fun i n T => τ i n T.obj) (fun i n _ _ φ x => hτ i n φ.hom x)
    (fun i n n' T x => hadd i n n' T.obj x) (fun i r n T x => hsm i r n T.obj x)
    (fun α T => W α T.obj) (fun α T => W' α T.obj)
    (fun α _ T' φ hT => hW α φ.hom hT T'.property) (fun α _ T' φ hT => hW' α φ.hom hT T'.property)
    (fun T => T.property) (fun T => T.property) (fun α T hT => h α T.obj hT) ?_ j
  intro S hS j
  obtain ⟨α₀, hα₀⟩ := hS
  have hP : capS W S ≤ U := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  have hP' : capS W' S ≤ U' := fun T hT => ⟨α₀, hT α₀ hα₀⟩
  refine tens_transfer (fun i => isoH (F i) hP j) (isoH F' hP' j).toAddEquiv (fun i n x => ?_) (hyp S ⟨α₀, hα₀⟩ j)
  exact isoH_morU (⟨G, τ i n, hτ i n⟩ : CH.Mor (F i) F' σ) hUU (fun T hT α hα => h α T (hT α hα)) hP hP' j x

end GlobalTheory.CompanionTheory.CosieveRel
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeUnit

theorem yQ_appLE_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m)
    (W : X.Opens) (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k') :
    IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  have ha : y k' ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hb : y k ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have ha1 : y k' ∈ grK K N (1 • e) := by simpa using ha
  have hb1 : y k ∈ grK K N (1 • e) := by simpa using hb
  have hVx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k' * y k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h2 h1
  have e1 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))
    (Proj.awayMap_awayToSection (grK K N) hb (x := y k' * y k) rfl)
  have e2 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1))
    (Proj.awayMap_awayToSection (grK K N) ha (x := y k' * y k) (mul_comm _ _))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  have e3 : (i.appLE _ W h2).hom (yQ y hy k k') = (i.appLE _ W hVx).hom
      ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) hb (x := y k' * y k) rfl
          (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))) := by
    rw [e1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  refine IsUnit.of_mul_eq_one ((i.appLE _ W hVx).hom ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) ha (x := y k' * y k) (mul_comm _ _)
          (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1)))) ?_
  rw [e3, ← map_mul, ← map_mul, GlobalTheory.CompanionTheory.GeoUnit.awayMap_ratio_mul ha hb hb1 ha1, map_one, map_one]

end GlobalTheory.CompanionTheory.ConeUnit
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_opens_cover_of_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | exact GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | (intros; apply GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.torus_monomial_mem_range : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), 0 < e → ∀ (S : Finset (Fin (d + 1))) (hS : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)) (ht : ∀ k, IsUnit (tV i y hy V hV k)), ∀ m ∈ expS S, tpow (fun k => (ht k).unit) m ∈ Set.range (evV i (yS y S) V hS) := by
  first | exact @GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | exact GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range | (intros; apply GlobalTheory.CompanionTheory.GeoTpow.tpow_mem_range <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Rep
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem rep_add {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z' c') :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => z s + z' s) (c + c') := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  refine ⟨f + f', by rw [map_add (f := _), hf, hf', add_zero], rfl, fun s => ?_⟩
  rw [map_add (f := _), ← hv, ← hv']
  rfl

theorem rep_smul {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (r : R) (h : CrystallineSemistableComparison.Pb.Rep a b z c) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => r • z s) (r • c) := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  have e : Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (r • z s) = r • Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (z s) := rfl
  rw [e, ← hv]
  rfl

theorem rep_congr {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (e : ∀ s, z s - z' s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z' c := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  exact ⟨f, hf, rfl, fun s => (hv s).trans (Ideal.Quotient.eq.2 (e s))⟩

theorem rep_unique {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)
  subst e
  rfl

theorem rep_zero {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    (e : ∀ s, z s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z 0 := by
  refine ⟨0, map_zero _, ?_, fun s => ?_⟩
  · exact (Submodule.Quotient.mk_zero _).symm
  · exact (Ideal.Quotient.eq_zero_iff_mem.2 (e s)).symm

theorem d_val {a b : IdF A} {j : ℕ} (f : CH.Cn (sq a b) j) (z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j)))
    (hv : ∀ s, (show sqM a b _ from f s).1 = Ideal.Quotient.mk _ (z s)) (s : ComposableArrows C (j + 1)) :
    (show sqM a b _ from CH.d _ j f s).1 = Ideal.Quotient.mk _
      (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s))) := by

  rw [map_sum]
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (f (face i s)) :
      sqM a b _) = _
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (f (face i s))).1 = _
  rw [GlobalTheory.CompanionTheory.GrDelta.sqMap_val a b _ _ _ (hv _)]

theorem rep_exists {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _)
    (hd : ∀ s, CH.d _ j g s ∈ b.S _) : ∃ c, CrystallineSemistableComparison.Pb.Rep a b (fun s => g s) c := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  have hd0 : CH.d _ j f = 0 := by
    funext s
    refine Subtype.ext ?_
    rw [d_val f (fun s => g s) (fun _ => rfl)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hd s)
  exact ⟨_, f, hd0, rfl, fun _ => rfl⟩

theorem rep_d {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => CH.d _ j g s) 0 := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  refine ⟨CH.d _ j f, CH.d_d _ j f, ?_, fun s => d_val f (fun s => g s) (fun _ => rfl) s⟩
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).symm
  change CH.d _ j f ∈ (CH.cx _).B (j + 1)
  exact ⟨f, rfl⟩

end Rep

end GlobalTheory.CompanionTheory.ConeLocal

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Res
variable {b : Base} {L : b.Fun}

theorem rep_res {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) {j : ℕ}
    {z : ∀ s : ComposableArrows Q.FullSubcategory j, (sP Q).A.obj (s.obj (Fin.last j))} {x : HQ Q r r' j}
    (hx : CrystallineSemistableComparison.Pb.Rep (sFil Q r) (sFil Q r') z x) :
    CrystallineSemistableComparison.Pb.Rep (sFil Q' r) (sFil Q' r') (fun s => z (s ⋙ ObjectProperty.ιOfLE h))
      (((incl h).sq (incl_fil _ r) (incl_fil _ r')).pull j x) := by
  obtain ⟨f, hf, rfl, hv⟩ := hx
  refine ⟨((incl h).sq (incl_fil _ r) (incl_fil _ r')).pullC j f, ?_, rfl, fun s => ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · change Ideal.quotientMap _ _ _ (show sqM _ _ _ from f (s ⋙ ObjectProperty.ιOfLE h)).1 = _
    rw [hv]
    rfl

def resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.Cn (CH.modF (sP Q').A) k :=
  fun s => f (s ⋙ ObjectProperty.ιOfLE h)

theorem d_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.d _ k (resQ h f) = resQ h (CH.d _ k f) :=
  (CH.Mor.d_pullC (⟨ObjectProperty.ιOfLE h, fun _ => LinearMap.id, fun _ _ => rfl⟩ :
    CH.Mor (CH.modF (sP Q).A) (CH.modF (sP Q').A) (RingHom.id _)) k f)

theorem cup_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (ℓ : Fin k → CH.Cn (CH.modF (sP Q).A) 1) :
    resQ h (cupListC (sP Q).A ℓ) = cupListC (sP Q').A fun i => resQ h (ℓ i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    have e := ih fun i => ℓ (Fin.castSucc i)
    change _ = (CH.mulP (sP Q').A).cupC _ (cupListC (sP Q').A fun i => resQ h (ℓ (Fin.castSucc i))) (resQ h (ℓ (Fin.last k))) s
    rw [← e]
    rfl

end Res

section Frames
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def Taylor (Fil : ℤ → IdF Φ.A) {d : ℕ} (E : Frame Φ d) (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) : Prop :=
  ∀ (T : C) (u v : E.D ⟶ T) (x : Φ.A.obj E.D),
    (Φ.A.map u).hom x - (Φ.A.map v).hom x - ∑ k, E.τ k v u * (Φ.A.map v).hom (p k x) ∈ (Fil 2).S T

def sgn {m d : ℕ} (I : Idx m d) (J : Fin m → Fin d) : ℤ :=
  ∑ π : Equiv.Perm (Fin m), if J = I.1 ∘ π then (Equiv.Perm.sign π : ℤ) else 0

end Frames

section Loc
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def IsLoc (s : ℕ) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D) : Prop :=
  E.GrConst (sFil (KS q s {W})) ∧
  (∀ x, x ∈ (sFil (KS q s {W}) 1).S E.D → x = 0) ∧
  (∀ a : K, ε (strV q W a) = algebraMap K ((sP (KS q s {W})).A.obj E.D) a) ∧
  (∀ (T : (KS q s {W}).FullSubcategory) (u : E.D ⟶ T) (g : Γ(X, W)),
    ev T.obj (ks_in q s W _ T.property) g = Ideal.Quotient.mk T.obj.J (((sP (KS q s {W})).A.map u).hom (ε g))) ∧
  ∀ (i : Fin d) {T : (KS q s {W}).FullSubcategory} (u v : E.D ⟶ T),
    E.τ i u v = ((sP (KS q s {W})).A.map v).hom (ε (t i)) - ((sP (KS q s {W})).A.map u).hom (ε (t i))

end Loc
end GlobalTheory.CompanionTheory.ConeLocal
end
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.graded_cohomology_of_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : CrystallineSemistableComparison.Pb.Frame Φ 0)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := Limits.IsInitial.ofUniqueHom σ fun _ f =>
    (E.bij f (fun _ => 0) (fun _ => Ideal.zero_mem _)).unique
      (fun i => i.elim0) (fun i => i.elim0)
  have hSucc (n : ℕ) : Subsingleton (CH.H (gr Fil r) (n + 1)) :=
    GlobalTheory.CompanionTheory.LocGr.H_succ_subsingleton _ hI n
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero =>
      exact GlobalTheory.CompanionTheory.LocGr.H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact hSucc n
  · cases j with
    | succ n =>
      have : Subsingleton (CH.H (gr Fil r) (n + 1)) := hSucc n
      have : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩,
        fun _ _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      have : Unique (Idx 0 0) :=
        ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0) :
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        rw [Fintype.sum_unique]
        simp [CrystallineSemistableComparison.Pb.Frame.form]
      refine ⟨fun c => ?_, fun x _ hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ :=
          (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf
                ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst f
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]
          rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cup_product_respects_hodge_filtration : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (i j : ℕ),
    (∃ b : HdR q i →ₗ[K] HdR q j →ₗ[K] HdR q (i + j), ∀ x y, b x y = cupK q rfl x y) ∧
    ∀ r s, ∀ x ∈ FilR q i r, ∀ y ∈ FilR q j s, cupK q rfl x y ∈ FilR q (i + j) (r + s) := by
  first | exact @GlobalTheory.CompanionTheory.CupdR.cup_bilinear_filtered | exact GlobalTheory.CompanionTheory.CupdR.cup_bilinear_filtered | (intros; apply GlobalTheory.CompanionTheory.CupdR.cup_bilinear_filtered <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.unit_class_ne_zero_of_nonempty : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | exact GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero <;> assumption)
end

section

open DividedPowers CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.lattice_filtration_comap_span_pow : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), ∀ r : ℕ, pdP (Lat.γ f ξ l M hc) r = (Ideal.span {f ξ ^ r}).comap (Lat.ι f ξ l M) := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq | exact GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq | (intros; apply GlobalTheory.CompanionTheory.LatPdpEq.dividedPowerFiltration_eq <;> assumption)
end
