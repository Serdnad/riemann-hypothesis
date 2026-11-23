module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle001
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle002
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle001
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

section

open CategoryTheory

namespace GlobalTheory

theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

end GlobalTheory
end

section

namespace GlobalTheory.ExistsEigenvector

theorem exists_eigenvector {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {U : Set G} (hU : IsOpen U)
    (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθ : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hne : ∑ i, T i (y i) ≠ 0) (heq : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v := by
  classical
  have hone : θ 1 = 1 := hθ 1 h1 K.one_mem
  have hθne : ∀ a ∈ K, θ a ≠ 0 := fun a ha h0 => by
    have := hmul a ha a⁻¹ (K.inv_mem ha)
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup K :=
    { carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, fun i => ?_⟩
        · rw [Subgroup.coe_mul, hmul _ a.2 _ b.2, ha, hb, one_mul]
        · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := ⟨hone, fun i => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, fun i => ?_⟩
        · have := hmul _ a.2 _ (K.inv_mem a.2)
          rw [mul_inv_cancel, hone, ha, one_mul] at this
          exact this.symm
        · conv_lhs => rw [← ha' i]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
  have hHo : IsOpen (H : Set K) := by
    have ho : IsOpen ((fun k : K => (k : G)) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      (hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))).preimage continuous_subtype_val
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨h1, by simp⟩) ?_)
    rintro k ⟨hk, hk'⟩
    exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : K → ι → V := fun k i => (θ k)⁻¹ • ρ k (y i)
  have hf : ∀ a b : K, QuotientGroup.leftRel H a b → f a = f b := by
    intro a b hab
    obtain ⟨h, h'⟩ : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have e : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
    funext i
    simp only [f]
    rw [e, hmul _ a.2 _ (a⁻¹ * b).2, h, mul_one, map_mul, Module.End.mul_apply, h']
  let F : K ⧸ H → ι → V := fun q => Quotient.liftOn' q f hf
  have hF : ∀ (h : K) (q : K ⧸ H) (i : ι), ρ h (F q i) = θ h • F (h • q) i := by
    intro h q i
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ρ h ((θ k)⁻¹ • ρ k (y i)) = θ h • ((θ (h * k))⁻¹ • ρ (h * k) (y i))
      rw [hmul _ h.2 _ k.2, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_inv,
        mul_inv_cancel_left₀ (hθne _ h.2)]
  have hT : ∀ q : K ⧸ H, ∑ i, T i (F q i) = ∑ i, T i (y i) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ∑ i, T i ((θ k)⁻¹ • ρ k (y i)) = _
      simp only [map_smul]
      rw [← Finset.smul_sum, heq _ k.2, smul_smul, inv_mul_cancel₀ (hθne _ k.2), one_smul]
  have hex : ∃ i, ∑ q, F q i ≠ 0 := by
    by_contra hc
    have hc' : ∀ i, ∑ q, F q i = 0 := fun i => not_not.1 fun h => hc ⟨i, h⟩
    have h0 : ∑ i, T i (∑ q, F q i) = 0 := by simp [hc']

    simp only [map_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [hT] at h0
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 h0)
    · exact hne h0
  obtain ⟨i, hi⟩ := hex
  refine ⟨_, hi, fun h hh => ?_⟩

  rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun q _ => hF ⟨h, hh⟩ q i]
  exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (fun q : K ⧸ H => θ h • F q i)

end GlobalTheory.ExistsEigenvector
end

section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.Et.H0

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem sh : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)]
  have h : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)
  have h2 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1}) := by
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor _) h
  exact h2

def yonedaAdd (X : Scheme.{0}) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) ≃+ P.obj (op X) where
  toEquiv := (((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P).trans
    uliftYonedaEquiv
  map_add' _ _ := rfl

def eAdd (X : Scheme.{0}) : H R 0 X ≃+ C(X, R) :=
  (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R)).trans <|
  ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homAddEquiv _ (coef R)).trans <|
  (yonedaAdd R X (coef R).obj).trans <|
  ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift)

theorem eAdd_smul (X : Scheme.{0}) (r : R) (x : H R 0 X) : eAdd R X (r • x) = r • eAdd R X x := by
  have h1 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x) =
      ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x :=
    (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (freeOn R).obj X) (Y := coef R)).map_smul (ULift.up r) x
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x))))) =
    r • AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x))))
  rw [h1]
  have h2 : yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
      (ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) =
      ULift.up r • yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) := rfl
  rw [h2]
  exact (congrArg AddEquiv.ulift (LinearEquiv.map_smul (((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv) (ULift.up r) _)).trans rfl

def e (X : Scheme.{0}) : H R 0 X ≃ₗ[R] C(X, R) :=
  { eAdd R X with map_smul' := eAdd_smul R X }

end GlobalTheory.Et.H0
end
end

section

open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem gl_transitive_lattices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  intro O K _ _ _ _ _ _ _ r
  refine ⟨fun L => ?_, fun g L => (glMap_isLattice g L).toIsLattice⟩
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  haveI : Module.Finite O L.1 := Module.Finite.iff_fg.2 L.2.fg
  have hr : Module.finrank O L.1 = r := by
    simpa using ((Submodule.IsFullLattice.finrank_eq K L.1).trans (Module.finrank_fintype_fun_eq_card K))
  let b : Module.Basis (Fin r) O L.1 := Module.finBasisOfFinrankEq O L.1 hr
  let c : Module.Basis (Fin r) K (Fin r → K) := b.extendOfIsLattice K
  have hc : ∀ i, c i = (b i : Fin r → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  let e : (Fin r → K) ≃ₗ[K] (Fin r → K) := (Pi.basisFun K (Fin r)).equiv c (Equiv.refl _)
  have he : ∀ i, e (Pi.basisFun K (Fin r) i) = c i := fun i => by
    simpa using (Pi.basisFun K (Fin r)).equiv_apply i c (Equiv.refl _)
  let g : GL (Fin r) K :=
    ⟨LinearMap.toMatrix' (e : (Fin r → K) →ₗ[K] (Fin r → K)),
      LinearMap.toMatrix' (e.symm : (Fin r → K) →ₗ[K] (Fin r → K)),
      by rw [← LinearMap.toMatrix'_comp]; simp,
      by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) = (e : (Fin r → K) →ₗ[K] (Fin r → K)) :=
    Matrix.toLin'_toMatrix' _
  refine ⟨g, ?_⟩
  have h1 : Set.range (Subtype.val ∘ b) = L.1.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  change (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
    ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O) = L.1
  rw [hg, Submodule.map_span, ← Set.range_comp]
  have h2 : ((e : (Fin r → K) →ₗ[K] (Fin r → K)).restrictScalars O) ∘ (Pi.basisFun K (Fin r))
      = Subtype.val ∘ b := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [he, hc]
  rw [h2, h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.LatHecke
end

section

noncomputable section

namespace GlobalTheory.SatakeInv

open Matrix

variable {K : Type} [Field K] {r : ℕ}

def tinv : GL (Fin r) K →* GL (Fin r) K where
  toFun g := ⟨((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ, (g : Matrix (Fin r) (Fin r) K)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by ext i j; simp [Matrix.one_apply, eq_comm]
  map_mul' g h := by ext : 1; simp [_root_.mul_inv_rev, transpose_mul]

theorem tinv_val (g : GL (Fin r) K) :
    ((tinv g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_inv_val (g : GL (Fin r) K) :
    (((tinv g)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ :=
  rfl

theorem tinv_tinv (g : GL (Fin r) K) : tinv (tinv g) = g := by
  ext : 1
  rw [tinv_val, tinv_inv_val, transpose_transpose]

def scalGL (c : Kˣ) : GL (Fin r) K :=
  Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom c

theorem scalGL_val (c : Kˣ) :
    ((scalGL c : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = Matrix.scalar (Fin r) (c : K) := rfl

theorem scalGL_comm (c : Kˣ) (g : GL (Fin r) K) : scalGL c * g = g * scalGL c := by
  ext : 1
  simp only [Units.val_mul, scalGL_val]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)

theorem tinv_scalGL (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = scalGL c⁻¹ := by
  ext : 1
  have h : (scalGL c : GL (Fin r) K)⁻¹ = scalGL c⁻¹ := (map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c).symm
  rw [tinv_val, h, scalGL_val, Matrix.scalar_apply, Matrix.diagonal_transpose]

theorem tinv_scalGL' (c : Kˣ) : tinv (scalGL c : GL (Fin r) K) = (scalGL c)⁻¹ := by
  rw [tinv_scalGL]
  exact map_inv (Units.map (Matrix.scalar (Fin r) : K →+* Matrix (Fin r) (Fin r) K).toMonoidHom) c

theorem tinv_injective : Function.Injective (tinv : GL (Fin r) K → GL (Fin r) K) := fun a b h => by
  rw [← tinv_tinv a, h, tinv_tinv]


omit [Field K] in
theorem glMap_eq_glMap_iff {O : Type} [CommRing O] [Field K] [Algebra O K] (a b : GL (Fin r) K)
    (L : Submodule O (Fin r → K)) :
    GlobalTheory.LatHecke.glMap a L = GlobalTheory.LatHecke.glMap b L ↔ GlobalTheory.LatHecke.glMap (a⁻¹ * b) L = L := by
  constructor
  · intro h
    rw [GlobalTheory.LatHecke.glMap_mul, ← h, ← GlobalTheory.LatHecke.glMap_mul, inv_mul_cancel, GlobalTheory.LatHecke.glMap_one]
  · intro h
    conv_lhs => rw [← h, ← GlobalTheory.LatHecke.glMap_mul, mul_inv_cancel_left]

theorem esymm_inv_mul_esymm_card (β : Multiset ℂ) (hβ : ∀ b ∈ β, b ≠ 0) {k : ℕ} (hk : k ≤ β.card) :
    (β.map (·⁻¹)).esymm k * β.esymm β.card = β.esymm (β.card - k) := by
  obtain ⟨n, α, rfl⟩ : ∃ (n : ℕ) (α : Fin n → ℂ), β = Finset.univ.val.map α := by
    induction β using Quotient.inductionOn with
    | h l => exact ⟨l.length, l.get, by simp⟩
  have hα : ∀ i, α i ≠ 0 := fun i => hβ _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  have hn : (Finset.univ.val.map α).card = n := by simp
  rw [hn] at hk ⊢
  simp only [Multiset.map_map, Finset.esymm_map_val, Function.comp_def]
  have h1 : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [h1, Finset.sum_singleton, Finset.sum_mul]
  refine Finset.sum_nbij' compl compl (fun t ht => ?_) (fun t ht => ?_) (by simp) (by simp) fun t _ => ?_
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    simp [Finset.card_compl, ht]
  · simp only [Finset.mem_powersetCard_univ] at ht ⊢
    rw [Finset.card_compl, ht, Fintype.card_fin]; omega
  · rw [← Finset.prod_mul_prod_compl t, ← mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun i _ => inv_mul_cancel₀ (hα i)), Finset.prod_const_one, one_mul]

end GlobalTheory.SatakeInv
end
end

section

namespace GlobalTheory.LowerBlockFlag

def f0 {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) × Fin (d i) ≃ Fin a) (c : Fin s) :
    Submodule k (Fin a → k) where
  carrier := {v | ∀ p : Fin a, c < GlobalTheory.SmGL.blk e p → v p = 0}
  add_mem' {u v} hu hv p hp := by
    rw [Pi.add_apply, hu p hp, hv p hp, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r {v} hv p hp := by
    rw [Pi.smul_apply, hv p hp, smul_zero]

end GlobalTheory.LowerBlockFlag
end

section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CenOrderIso

def toLocal (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* ℚ_[ℓ] ⊗[ℚ] F :=
  (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.toRingEquiv.toRingHom.comp
    ((Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom).toRingHom)

theorem toLocal_tmul (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (c : 𝓞 F) (a : ℤ_[ℓ]) :
    toLocal F ℓ (c ⊗ₜ[ℤ] a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := rfl

theorem toLocal_injective (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (toLocal F ℓ) := by
  have h1 : Function.Injective
      ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
  have h2 : Function.Injective
      ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 F) F)
  have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) := by
    have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) =
        ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) ∘
        ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) := by
      funext w
      induction w using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢; rw [ha, hb]
    rw [this]; exact h2.comp h1
  intro x y hxy
  apply hmap
  apply (Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).injective
  exact (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.injective hxy

theorem toLocal_mem (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (x : 𝓞 F ⊗[ℤ] ℤ_[ℓ]) :
    toLocal F ℓ x ∈ cenOrder ℓ F := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [toLocal_tmul]
    have hc : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) ∈ cenOrder ℓ F :=
      Algebra.subset_adjoin ⟨c, rfl⟩
    have : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) = a • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F)) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      show (a : ℚ_[ℓ]) = a • (1 : ℚ_[ℓ])
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Subalgebra.smul_mem _ hc a
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem cenOrder_le_range (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ y ∈ cenOrder ℓ F, ∃ x, toLocal F ℓ x = y := by
  let S : Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
    { (toLocal F ℓ).range with
      algebraMap_mem' := fun r => ⟨(1 : 𝓞 F) ⊗ₜ[ℤ] r, by
        rw [toLocal_tmul]; rfl⟩ }
  have hle : cenOrder ℓ F ≤ S := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact ⟨c ⊗ₜ[ℤ] (1 : ℤ_[ℓ]), by rw [toLocal_tmul]; simp⟩
  intro y hy
  exact hle hy

theorem cenOrder_equiv : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F,
      ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  intro F _ _ ℓ _
  let g : 𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* cenOrder ℓ F := (toLocal F ℓ).codRestrict (cenOrder ℓ F) (toLocal_mem F ℓ)
  have hbij : Function.Bijective g := by
    refine ⟨fun x y h => toLocal_injective F ℓ (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := cenOrder_le_range F ℓ y y.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g hbij, fun c => ?_⟩
  show toLocal F ℓ (c ⊗ₜ[ℤ] 1) = _
  rw [toLocal_tmul]; simp

end GlobalTheory.CenOrderIso
end
end

section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem isEmpty_of_fibrePointsLE_zero {Z X : Scheme.{0}} (f : Z ⟶ X) (h : FibrePointsLE f 0) :
    IsEmpty Z := by
  refine ⟨fun z => ?_⟩
  exact h (Z.residueField z) (Z.fromSpecResidueField z ≫ f) (fun _ => Z.fromSpecResidueField z)
    (fun _ => rfl) (fun a b _ => Fin.subsingleton_one.elim a b)

end GlobalTheory.EtC.Tr
end

section


theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_le_of_recurrence_growth' : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  first | exact @GlobalTheory.norm_le_of_recurrence_growth | exact GlobalTheory.norm_le_of_recurrence_growth | (intros; apply GlobalTheory.norm_le_of_recurrence_growth <;> assumption)
end
