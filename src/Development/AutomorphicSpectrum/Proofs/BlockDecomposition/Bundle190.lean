module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle173
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle183
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeRepCup

open GlobalTheory.CompanionTheory.CupRep

theorem cupList_cocycle {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) :
    ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → CH.d _ m (cupListC A ℓ) = 0
  | 0, _, _ => by
      funext s
      change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom 1 = (0 : A.obj _)
      rw [Fin.sum_univ_two, map_one, map_one]
      simp
  | m + 1, ℓ, h => by
      change CH.d _ (m + 1) ((CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last m))) = 0
      rw [CrystallineSemistableComparison.P.leibniz, cupList_cocycle A _ (fun k => h _), h]
      simp

theorem cupList_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m
  | 0, _, _ => mem_FC.2 fun s => by
      rw [Nat.cast_zero, hF.top 0 le_rfl]
      exact trivial
  | m + 1, ℓ, h => cup_mem hF (r := m) (r' := 1) _ (cupList_mem hF _ fun k => h _) (h _)

theorem exists_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) :
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  intro hF m ℓ hd hl
  have hm : cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m :=
    cupList_mem hF ℓ fun k => mem_FC.2 fun s => by simpa using hl k s
  refine GlobalTheory.CompanionTheory.ConeLocal.rep_exists (cupListC Φ.A ℓ) (mem_FC.1 hm) fun s => ?_
  rw [cupList_cocycle Φ.A ℓ hd]
  exact (Fil ((m : ℤ) + 1)).S _ |>.zero_mem

end GlobalTheory.CompanionTheory.ConeRepCup
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Cap
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_mono {V W : X.Opens} (h : V ≤ W) (T : Thick (smFun X q))
    (hT : InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V T) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) W T :=
  fun x hx => h (hT hx)

theorem coe_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    ((capO U i : X.Opens) : Set X) = ⋂ k, (U (i k) : Set X) := by
  have h : capO U i = Finset.univ.inf fun k => U (i k) := by
    rw [Finset.inf_univ_eq_iInf]; rfl
  rw [h, TopologicalSpace.Opens.coe_finset_inf]
  ext x
  simp [Finset.inf_eq_iInf]

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (smFun X q)) :
    InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (capO U i) T ↔
      ∀ k, InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U (i k)) T := by
  constructor
  · exact fun h k => inU_mono q (capO_le U i k) T h
  · intro h x hx
    have : (pt T x) ∈ ((capO U i : X.Opens) : Set X) := by
      rw [coe_capO]
      exact Set.mem_iInter.2 fun k => h k hx
    exact this

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

theorem kc_of_ks (T : Thick (smFun X q)) (h : KS q (a + 1) {capO U.U i} T) : KC q U a T := by
  obtain ⟨h1, V, rfl, h2⟩ := h
  exact ⟨h1, U.U (i 0), ⟨_, rfl⟩, inU_mono q (capO_le U.U i 0) T h2⟩

theorem ks_of_cap (T : (KC q U a).FullSubcategory) (h : capT (Vk q U a) i T) : KS q (a + 1) {capO U.U i} T.obj :=
  ⟨T.property.1, _, rfl, (inU_capO q U.U i T.obj).2 h⟩

def capG : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T => kc_of_ks q U a n i _ T.property)
    fun T => by
      obtain ⟨h1, V, rfl, h2⟩ := T.property
      exact (inU_capO q U.U i T.obj).1 h2

def capH : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T => ks_of_cap q U a n i T.obj T.property

def capE : (KS q (a + 1) {capO U.U i}).FullSubcategory ≌ (capT (Vk q U a) i).FullSubcategory :=
  CategoryTheory.Equivalence.mk (capG q U a n i) (capH q U a n i)
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl))

def capM : CH.Mor ((capT (Vk q U a) i).ι ⋙ Fk q U a) ((KS q (a + 1) {capO U.U i}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) where
  G := capG q U a n i
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem capM_bij (r : ℕ) : Function.Bijective ((capM q U a n i).pull r) := by
  haveI : (capM q U a n i).G.IsLeftAdjoint := (capE q U a n i).isLeftAdjoint_functor
  exact CrystallineSemistableComparison.P.adj_mor (capM q U a n i) (fun _ => Function.bijective_id) r

end Cap
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Nat
variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem ks_pull (u : X ⟶ Y) (hu : u ≫ p = q) {V : X.Opens} {W : Y.Opens} (h : V ≤ u ⁻¹ᵁ W) (s a : ℕ) (T : Thick (smFun X q))
    (hT : KS q s {V} T) : KS p s {W} ((pullM u hu a).G.obj T) := by
  obtain ⟨h1, V', rfl, h2⟩ := hT
  exact ⟨h1, W, rfl, fun x hx => h (h2 hx)⟩

theorem capM_res (U : Cov q) (a m n : ℕ) (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1))
    (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a) :
    (capM q U a n i).pull a ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
      (resU (HT.grT (smFun X q) a) (U := KS q (a + 1) {capO U.U (i ∘ θ)}) (V := KS q (a + 1) {capO U.U i}) (by
        rintro T ⟨h1, V', rfl, h2⟩
        exact ⟨h1, _, rfl, inU_mono q (capO_comp U.U i θ) T h2⟩)).pull a ((capM q U a m (i ∘ θ)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem capM_pull (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
    (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T)) (n : ℕ) (i : Fin (n + 1) → U.ι)
    (hG' : ∀ T, capT (Vk q U a) i T →
      capT (Vk p W a) (τ ∘ i) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
    (h : ∀ T, KS q (a + 1) {capO U.U i} T → KS p (a + 1) {capO W.U (τ ∘ i)} ((pullM u hu a).G.obj T))
    (x : HU (Fk p W a) (capT (Vk p W a) (τ ∘ i)) a) :
    (capM q U a n i).pull a ((morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
        (U' := capT (Vk q U a) i) hG').pull a x) =
      (morU (pullM u hu a) (U := KS p (a + 1) {capO W.U (τ ∘ i)}) (U' := KS q (a + 1) {capO U.U i}) h).pull a
        ((capM p W a n (τ ∘ i)).pull a x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Nat
end GlobalTheory.CompanionTheory.OmGlobTerm

noncomputable section
namespace GlobalTheory.CompanionTheory.OmGlobTerm

section Id
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def idT (hu : 𝟙 X ≫ q = q) (T : Thick (smFun X q)) : T ⟶ (smMor (𝟙 X) hu).functor.obj T :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := (smMor (𝟙 X) hu).functor.obj T) (RingHom.id _) (fun _ => rfl) ⟨Ideal.map_le_iff_le_comap.2 (fun x hx => hx), fun x hx => rfl⟩ (fun x hx => hx) (by
    have e : CommRingCat.ofHom (Ideal.quotientMap ((smMor (𝟙 X) hu).functor.obj T).J (RingHom.id T.B) (fun x hx => hx)) = 𝟙 (CommRingCat.of (T.B ⧸ T.J)) := by
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => rfl))
    refine Eq.trans (congrArg (fun f => (ConcreteCategory.hom ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map f)) T.y) e) ?_
    refine Eq.trans (congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _)) ((nlFun (dividedPowersBot K) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map_id _)) T.y) ?_
    exact Subtype.ext (Prod.ext rfl (Category.comp_id _).symm))

theorem morU_id (hu : 𝟙 X ≫ q = q) (a : ℕ) (Q Q' : ObjectProperty (Thick (smFun X q)))
    (h : ∀ T, Q' T → Q ((pullM (𝟙 X) hu a).G.obj T)) (hle : Q' ≤ Q) (n : ℕ) (x) :
    (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h).pull n x = (resU (HT.grT (smFun X q) a) hle).pull n x := by
  symm
  refine CrystallineSemistableComparison.P.prism (resU (HT.grT (smFun X q) a) hle) (morU (pullM (𝟙 X) hu a) (U := Q) (U' := Q') h)
    { app := fun T => ObjectProperty.homMk (idT hu T.obj)
      naturality := fun T T' f => ?_ } ?_ n x
  · refine ObjectProperty.hom_ext _ ?_
    exact hom_ext (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) rfl
  · intro T x
    obtain ⟨y, hy, rfl⟩ := HT.sq_surj _ _ x
    rfl

end Id
end GlobalTheory.CompanionTheory.OmGlobTerm
end
end
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace GlobalTheory.CompanionTheory.CapKC

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem inU_capO {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) : InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  constructor
  · intro h a x hx
    exact capO_le U i a (h hx)
  · intro h x hx
    let W : X.Opens := ⟨⋂ a, (U (i a) : Set X), isOpen_iInter_of_finite fun a => (U (i a)).isOpen⟩
    have hW : W ≤ capO U i := le_iInf fun a y hy => Set.mem_iInter.1 hy a
    exact hW (Set.mem_iInter.2 fun a => h a hx)

variable (U : Cov q) (a n : ℕ) (i : Fin (n + 1) → U.ι)

def toCap : (KS q (a + 1) {capO U.U i}).FullSubcategory ⥤ (capT (Vk q U a) i).FullSubcategory :=
  (capT (Vk q U a) i).lift ((KC q U a).lift (KS q (a + 1) {capO U.U i}).ι fun T =>
      ⟨T.property.1, U.U (i 0), ⟨i 0, rfl⟩, by
        obtain ⟨_, V, rfl, hV⟩ := T.property
        exact (inU_capO U.U i T.obj).1 hV 0⟩) fun T k => by
    obtain ⟨_, V, rfl, hV⟩ := T.property
    exact (inU_capO U.U i T.obj).1 hV k

def ofCap : (capT (Vk q U a) i).FullSubcategory ⥤ (KS q (a + 1) {capO U.U i}).FullSubcategory :=
  (KS q (a + 1) {capO U.U i}).lift ((capT (Vk q U a) i).ι ⋙ (KC q U a).ι) fun T =>
    ⟨T.obj.property.1, capO U.U i, rfl, (inU_capO U.U i T.obj.obj).2 T.property⟩

def capAdj : toCap q U a n i ⊣ ofCap q U a n i := Adjunction.mkOfHomEquiv
  { homEquiv := fun A B =>
      { toFun := fun g => ObjectProperty.homMk g.hom.hom
        invFun := fun g => ObjectProperty.homMk (ObjectProperty.homMk g.hom)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    homEquiv_naturality_left_symm := fun _ _ => rfl
    homEquiv_naturality_right := fun _ _ => rfl }

theorem cap_kc : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  intro K _ X q U a n i r
  have hb := CrystallineSemistableComparison.P.adj ((capT (Vk q U a) i).ι ⋙ Fk q U a) (toCap q U a n i) (ofCap q U a n i) (capAdj q U a n i) r
  exact ⟨(LinearEquiv.ofBijective _ hb).toAddEquiv⟩

end GlobalTheory.CompanionTheory.CapKC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltCompl

variable {l : ℕ} [Fact l.Prime]

theorem norm_pFlat_pos : 0 < ‖pFlat l‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact norm_pos_iff.2 natCast_p_ne_zero_cp

theorem norm_pFlat_lt_one : ‖pFlat l‖ < 1 := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem smodEq_iff (n : ℕ) (x y : Ob l) :
    x ≡ y [SMOD (Ideal.span {pFlat l} ^ n • ⊤ : Ideal (Ob l))] ↔ ‖x - y‖ ≤ ‖pFlat l‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

theorem complete_tf : ∀ {l : ℕ} [Fact l.Prime],
    IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  intro l _
  have h0 : 0 < ‖pFlat l‖ := norm_pFlat_pos
  have h1 : ‖pFlat l‖ < 1 := norm_pFlat_lt_one
  have hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩
  · have hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n := fun n => by
      simpa using (smodEq_iff n x 0).1 (hx n)
    have : ‖x‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact norm_le_zero_iff.1 this
  · have hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m := fun h =>
      (smodEq_iff _ _ _).1 (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hb n.le_succ
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩
    have ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    refine le_of_tendsto ht ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm
  · exact mem_nonZeroDivisors_iff_left.2 fun x hx => by
      have := congrArg norm hx
      rw [norm_mul, norm_zero] at this
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')

end GlobalTheory.CompanionTheory.TiltCompl
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPiece

theorem subsingleton_tmul {O N M : Type} [CommRing O] [AddCommGroup N] [Module O N] [AddCommGroup M] [Module O M]
    [Subsingleton M] (y : N ⊗[O] M) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]


theorem main : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  intro O A G _ _ _ _ _ _ I γ m S u v M _ _ M' _ θ h0 π hπ hker f hf0 hf
  classical
  obtain ⟨g₀, hs, hm⟩ := GlobalTheory.T.graded_splitting_tensor_filtration (Γ := G) γ m S
  let t : ∀ i : Fin m, S.N i ⊗[O] M i →+ S.N i ⊗[O] G := fun i =>
    if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then
      ((LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm : S.N i ⊗[O] M i ≃ₗ[O] S.N i ⊗[O] G).toLinearMap.toAddMonoidHom
    else 0
  have t_act : ∀ (i : Fin m) (h : u ≤ (i : ℕ) ∧ (i : ℕ) < v) (a : S.N i ⊗[O] G),
      t i (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) a) = a := by
    intro i h a
    simp only [t, dif_pos h]
    exact (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm_apply_apply a
  have t_inact : ∀ (i : Fin m), ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → t i = 0 := by
    intro i h
    simp only [t, dif_neg h]
  let T : (∀ i, S.N i ⊗[O] M i) →+ (∀ i, S.N i ⊗[O] G) :=
    { toFun := fun w i => t i (w i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have T_apply : ∀ w i, T w i = t i (w i) := fun _ _ => rfl
  have hT : ∀ w, g₀ (T w) ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
    intro w
    refine (hm u _).2 fun i hi => ?_
    rw [T_apply, t_inact i (by omega)]
    rfl
  let φ : (∀ i, S.N i ⊗[O] M i) →+ M' :=
    { toFun := fun w => π ⟨g₀ (T w), hT w⟩
      map_zero' := by
        have : (⟨g₀ (T 0), hT 0⟩ : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        exact congrArg π (Subtype.ext (by simp)) }
  have φ_apply : ∀ w, φ w = π ⟨g₀ (T w), hT w⟩ := fun _ => rfl
  have inj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw => ?_
    rw [φ_apply] at hw
    have h1 := (hm v _).1 ((hker _).1 hw)
    funext i
    by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
    · have h2 := h1 i h.2
      rw [T_apply] at h2
      obtain ⟨a, ha⟩ := (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).surjective (w i)
      rw [← ha, t_act i h] at h2
      rw [← ha, h2, map_zero]
      rfl
    · haveI := h0 i h
      exact subsingleton_tmul _
  have surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨z, hz⟩ := g₀.surjective x.1
    have hzu := (hm u z).1 (by rw [hz]; exact x.2)
    let w : ∀ i, S.N i ⊗[O] M i := fun i =>
      if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) (z i) else 0
    refine ⟨w, ?_⟩
    rw [φ_apply, ← sub_eq_zero, ← map_sub, hker]
    have : ((⟨g₀ (T w), hT w⟩ - x : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) : A ⊗[O] G)
        = g₀ (T w - z) := by
      rw [map_sub, hz]
      rfl
    rw [this, hm]
    intro i hi
    rw [Pi.sub_apply, T_apply, sub_eq_zero]
    by_cases h : u ≤ (i : ℕ)
    · have h' : u ≤ (i : ℕ) ∧ (i : ℕ) < v := ⟨h, hi⟩
      simp only [w, dif_pos h']
      exact t_act i h' _
    · rw [t_inact i (by omega), hzu i (by omega)]
      rfl
  refine ⟨AddEquiv.ofBijective φ ⟨inj, surj⟩, fun i n x => ?_⟩
  rw [AddEquiv.ofBijective_apply]
  by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
  · obtain ⟨y, rfl⟩ := (θ i h.1 h.2).surjective x
    have hTs : T (Pi.single i (n ⊗ₜ[O] θ i h.1 h.2 y)) = Pi.single i (n ⊗ₜ[O] y) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [T_apply, Pi.single_eq_same, Pi.single_eq_same]
        exact t_act j h (n ⊗ₜ[O] y)
      · rw [T_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
    have hx : S.ν i n ⊗ₜ[O] y ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
      rw [← hs, ← hTs]
      exact hT _
    rw [hf i n y h.1 h.2 hx, φ_apply]
    exact congrArg π (Subtype.ext (by simp only [hTs, hs]))
  · haveI := h0 i h
    rw [Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero, hf0]

end GlobalTheory.CompanionTheory.GrPiece
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cone_cocycle_closed : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeZcoc.main | exact GlobalTheory.CompanionTheory.ConeZcoc.main | (intros; apply GlobalTheory.CompanionTheory.ConeZcoc.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.supremum_twisting_opens_eq_top : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace R N), IsTautologicalLineAt D N i → sSup (𝒱D D) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeCover.main | exact GlobalTheory.CompanionTheory.ConeCover.main | (intros; apply GlobalTheory.CompanionTheory.ConeCover.main <;> assumption)
end
