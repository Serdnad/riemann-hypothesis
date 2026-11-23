module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Mathlib.FieldTheory.Relrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle038
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  {Ω₀ Ω : Type*} [Field Ω₀] [Field Ω]

def scaleT (c : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k => C (c k) * X k

theorem scaleT_injective (c : K → Ω) (hc : ∀ k, c k ≠ 0) : Function.Injective (scaleT c) := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleT fun k => (c k)⁻¹) fun f => by
    simpa using congrArg (fun g => g f) h

theorem imageZ_mCoordIdeal_of_eq (κ : K → K') (hκ : Function.Injective κ) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (hv : ∀ p, (v p).1 = κ p.1) (φ : Ω₀ →+* Ω) (b : K → Ω) (hb : ∀ k, b k ≠ 0)
    (y₀ : (Σ k, ι k) → Ω₀) (y : (Σ k', ι' k') → Ω) (h : ∀ p, φ (y₀ p) = b p.1 * y (v p)) :
    imageZ v (Geo.mCoordIdeal y) = Geo.mCoordIdeal y₀ := by
  let ψ : MvPolynomial K Ω₀ →+* MvPolynomial K' Ω :=
    ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom.comp
      (scaleT fun k => (b k)⁻¹).toRingHom).comp (MvPolynomial.map φ)
  have hψ : Function.Injective ψ :=
    (rename_injective κ hκ).comp ((scaleT_injective _ fun k => inv_ne_zero (hb k)).comp
      (map_injective φ φ.injective))
  have key : ∀ f : Geo.MRing ι, ψ (Geo.mConeMap y₀ f) = Geo.mConeMap y (rename v f) := by
    intro f
    have e : ψ.comp (Geo.mConeMap y₀ : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω₀).toRingHom =
        ((Geo.mConeMap y : Geo.MRing ι' →ₐ[ℤ] MvPolynomial K' Ω).toRingHom.comp
          (rename v : Geo.MRing ι →ₐ[ℤ] Geo.MRing ι').toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · simp
      · simp only [ψ, Geo.mConeMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          rename_X, map_mul, map_C, map_X, scaleT, algHom_C, rename_C]
        rw [hv p, h p]
        simp only [MvPolynomial.algebraMap_eq, rename_C]
        rw [← mul_assoc, ← C_mul, mul_comm (b p.1), mul_assoc, mul_inv_cancel₀ (hb p.1), mul_one]
    exact congrArg (fun g => g f) e
  ext f
  simp only [imageZ, Geo.mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← key, map_eq_zero_iff ψ hψ]

end Alg

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem evaluation_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem ptCoord_qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (k : Fin (m + 1)) :
    ∃ b : (MP ℤ (m + 1) (consN n' n)).residueField x, b ≠ 0 ∧ ∀ i : Bk n k,
      (qpSnd n' m n).residueFieldMap x (ptCoord (qpSnd n' m n x) ⟨k, i⟩) = b * ptCoord x ⟨k.succ, i⟩ := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  let P : MP ℤ (m + 1) (consN n' n) ⟶ PSpace ℤ (n k) := prB (consN n' n) k.succ
  have hP : F ≫ prB n k = P := rfl
  let c₀ := ptChart (F x) k
  let c₁ := ptChart x k.succ
  have hx₀ : F x ∈ blockChart n k c₀ := mem_ptChart _ _
  have hx₁ : x ∈ blockChart (consN n' n) k.succ c₁ := mem_ptChart _ _
  let W₀ : (MP ℤ (m + 1) (consN n' n)).Opens := F ⁻¹ᵁ blockChart n k c₀
  let W₁ : (MP ℤ (m + 1) (consN n' n)).Opens := blockChart (consN n' n) k.succ c₁
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := le_rfl
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := inf_le_right.trans h₁
  have e₀ : ∀ i : Bk n k, F.residueFieldMap x (ptCoord (F x) ⟨k, i⟩) =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ i) := by
    intro i
    show F.residueFieldMap x ((MP ℤ m n).evaluation (blockChart n k c₀) (F x) hx₀
      (pullRatio (prB n k) _ c₀ le_rfl i)) = _
    rw [Scheme.evaluation_naturality_apply, Scheme.Hom.app_eq_appLE, appLE_pullRatio,
      ← evaluation_resG (inf_le_left : V ≤ W₀) x hxV, resG_pullRatio]
    rfl
  have e₁ : ∀ i : Bk n k, ptCoord x ⟨k.succ, i⟩ =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₁ hV₁ i) := by
    intro i
    show (MP ℤ (m + 1) (consN n' n)).evaluation W₁ x hx₁ (pullRatio P W₁ c₁ h₁ i) = _
    rw [← evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  refine ⟨(MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ c₁), ?_, fun i => ?_⟩
  · intro h0
    have e := congrArg ((MP ℤ (m + 1) (consN n' n)).evaluation V x hxV)
      ((pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := c₀)).trans pullRatio_self)
    rw [map_mul, h0, zero_mul, map_one] at e
    exact zero_ne_one e
  · refine (e₀ i).trans ?_
    rw [e₁ i, ← map_mul]
    exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := i)).symm

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem imageZ_ptIdeal (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) :
    imageZ (sv n' n) (ptIdeal x) = ptIdeal (qpSnd n' m n x) := by
  choose b hb h using ptCoord_qpSnd n' m n x
  exact imageZ_mCoordIdeal_of_eq Fin.succ (Fin.succ_injective _) (sv n' n) (fun _ => rfl)
    ((qpSnd n' m n).residueFieldMap x).hom b hb (ptCoord (qpSnd n' m n x)) (ptCoord x) fun p => h p.1 p.2

end GlobalTheory.CompanionTheory.MPDict.ProjImage
end
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.FnDeg

open GlobalTheory.ProjSpace

theorem eval_pullRatio_comp {X Y : Scheme.{0}} {N : ℕ} (g : X ⟶ Y) (ψ : Y ⟶ PSpace ℤ N) (x : X)
    (i : Fin (N + 1)) (hx : g x ∈ ψ ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    (g.residueFieldMap x).hom ((Y.evaluation (ψ ⁻¹ᵁ chart ℤ N i) (g x) hx).hom (pullRatio ψ _ i le_rfl j)) =
      (X.evaluation ((g ≫ ψ) ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio (g ≫ ψ) _ i le_rfl j) := by
  have h1 := Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)
  have h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_pullRatio (hi := le_rfl) g le_rfl
  exact h1.trans (congrArg _ h2)

theorem closure_eval_ratio {N : ℕ} (p : PSpace ℤ N) (i : Fin (N + 1)) (hp : p ∈ chart ℤ N i) :
    Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j)) = ⊤ := by
  set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))
  have hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K := by
    intro s
    obtain ⟨q, rfl⟩ := aeval_ratio_surjective ℤ N i s
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      simpa using K.intCast_mem a
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact K.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul, aeval_X]
      exact K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)
  let ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K)
      (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)
  refine GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K
    (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_
  rw [← Category.assoc, ← Spec.map_comp]
  have hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec =
      (PSpace ℤ N).fromSpecResidueField p := by
    rw [Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp,
      IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]
  exact hev

theorem range_residueFieldMap_le {X : Scheme.{0}} {N : ℕ} (φ : X ⟶ PSpace ℤ N) (x : X) (i : Fin (N + 1))
    (hx : x ∈ φ ⁻¹ᵁ chart ℤ N i) :
    Set.range (φ.residueFieldMap x).hom ⊆
      Subfield.closure (Set.range fun j => (X.evaluation (φ ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio φ _ i le_rfl j)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subfield.closure (Set.range fun j =>
      ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j)) := by
    have hc := closure_eval_ratio (φ x) i hx
    rw [hc]
    exact Subfield.mem_top a
  have h1 : (φ.residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
  rw [RingHom.map_field_closure] at h1
  refine Subfield.closure_mono ?_ h1
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  have h2 := Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)
  rw [Scheme.Hom.app_eq_appLE] at h2
  exact h2.symm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp only [ptCoord, pullRatio_self, map_one]

theorem range_prB_le (x : MP ℤ m n) (k : Fin (m + 1)) :
    Set.range ((prB n k).residueFieldMap x).hom ⊆ Subfield.closure (Set.range (ptCoord x)) := by
  refine (range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_
  refine Subfield.closure_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩

abbrev sndM (m : ℕ) (n : Fin (m + 2) → ℕ) : MP ℤ (m + 1) n ⟶ MP ℤ m (Fin.tail n) :=
  pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))

theorem residueFieldMap_ptCoord_sndM {n : Fin (m + 2) → ℕ} (x : MP ℤ (m + 1) n) (k : Fin (m + 1))
    (j : Bk (Fin.tail n) k) :
    ((sndM m n).residueFieldMap x).hom (ptCoord (sndM m n x) ⟨k, j⟩) = ptCoord x ⟨k.succ, j⟩ :=
  eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j

theorem closure_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n),
    Subfield.closure (Set.range (ptCoord x)) = ⊤
  | 0, n, x => by
    haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _))
    refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_
    exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a
  | m + 1, n, x => by
    have H : Subfield.closure (Set.range ((prB n 0).residueFieldMap x).hom ∪
        Set.range ((sndM m n).residueFieldMap x).hom) = ⊤ :=
      GlobalTheory.closure_range_residueFieldMap_pullback_eq_top _ _ _ (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) x
    rw [eq_top_iff, ← H]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact range_prB_le x 0 ⟨a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      have ha : a ∈ Subfield.closure (Set.range (ptCoord (sndM m n x))) := by
        rw [closure_ptCoord m (Fin.tail n) (sndM m n x)]
        exact Subfield.mem_top a
      have h1 : ((sndM m n).residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
      rw [RingHom.map_field_closure] at h1
      refine Subfield.closure_mono ?_ h1
      rintro _ ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
      exact ⟨⟨k.succ, j⟩, (residueFieldMap_ptCoord_sndM x k j).symm⟩

theorem blockFnField_ptCoord (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)] :
    blockFnField (ptCoord x) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨p, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩
    rw [ptCoord_ptChart, div_one]
  exact hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)

theorem blockFnField_comp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω Ω' : Type*} [Field Ω]
    [CharZero Ω] [Field Ω'] [CharZero Ω'] (g : Ω →ₐ[ℚ] Ω') (y : (Σ k, ι k) → Ω) :
    blockFnField (g ∘ y) = (blockFnField y).map g := by
  unfold blockFnField
  rw [IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp [map_div₀]⟩

theorem ptCoord_sv (n' : ℕ) {m : ℕ} (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (p : Σ k, Bk n k) :
    ptCoord x (sv n' n p) = ((qpSnd n' m n).residueFieldMap x).hom (ptCoord ((qpSnd n' m n) x) p) :=
  (residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm

theorem relfinrank_blockFnField_sv : ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)],
    IntermediateField.relfinrank (blockFnField (ptCoord x ∘ sv n' n)) (blockFnField (ptCoord x)) =
      (qpSnd n' m n).residueDegree x := by
  intro n' m n x _
  let f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x :=
    (qpSnd n' m n).residueFieldMap x
  haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) :=
    (RingHom.charZero_iff f.hom.injective).2 inferInstance
  let g := f.hom.toRatAlgHom
  have e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x) := _root_.funext fun p => ptCoord_sv n' n x p
  rw [e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]
  letI := f.hom.toAlgebra
  let i := (IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm
  ext a
  rfl

end GlobalTheory.CompanionTheory.MPDict.FnDeg
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CoefWeight

theorem continuous_norm_coefChar : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ β : PositivityTheory.GramSchwartzFunctions.HermE D n, Continuous (fun b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n => ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))) ∧ ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ‖ψ (-GlobalTheory.StdUnn.halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))‖ = 1 := by
  intro D n ψ hψ β
  refine ⟨?_, fun b => hψ.2.1 _⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  unfold GlobalTheory.StdUnn.halfTr
  exact hψ.1.comp ((continuous_const.mul (ht.comp
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace))).neg)

end GlobalTheory.CompanionTheory.CoefWeight
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

theorem rat_mem_hermA (β : HermE D r) : rat β.1 ∈ hermA D r := by
  show adj (rat β.1) = rat β.1
  rw [← rat_conjTranspose]
  congr 1
  exact β.2

def ofHermE (β : HermE D r) : ratHerm D r :=
  ⟨⟨rat β.1, rat_mem_hermA β⟩, ⟨β.1, rfl⟩⟩

theorem ofHermE_val (β : HermE D r) : (ofHermE β).1.1 = β.1.map (incA D) := rfl

theorem ofHermE_bijective : Function.Bijective (ofHermE (D := D) (r := r)) := by
  refine ⟨fun a b h => Subtype.ext (rat_injective (congrArg (fun c : ratHerm D r => c.1.1) h)), ?_⟩
  rintro ⟨⟨x, hx⟩, hr⟩
  obtain ⟨γ, hγ⟩ := (mem_ratMx).1 (AddSubgroup.mem_comap.1 hr)
  have hγ' : rat γ = x := hγ
  refine ⟨⟨γ, rat_injective ?_⟩, Subtype.ext (Subtype.ext hγ')⟩
  have hx' : adj x = x := hx
  have : rat γᴴ = rat γ := by rw [rat_conjTranspose, hγ', hx']
  exact this

def hermEquiv : HermE D r ≃ ratHerm D r := Equiv.ofBijective _ ofHermE_bijective

theorem W_eq (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) :
    W ψ V μ lam φ β = ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul (ofHermE β).1.1 b.1 : Mx D r r))) ∂lam := rfl

end GlobalTheory.CompanionTheory.HermPoisson
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel

theorem bigCell_of_poisson_siegel :
    (∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖) → PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm → (∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ)) → PositivityTheory.GramSchwartzFunctions.BC.SiegelND → PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg → PositivityTheory.GramSchwartzFunctions.BigCell := by
  intro hlam hP hG hND hDeg D r V h2r ψ hψ θ hθ μ 𝓕 h𝓕 ν hν φ hφ habs hsum
  obtain ⟨lam, 𝓖, hlg⟩ := hlam D r
  have hyp : Hyp D r V ψ θ μ lam ν φ :=
    ⟨h2r, hψ, hθ, ⟨𝓕, h𝓕⟩, ⟨𝓖, hlg⟩, hν, hφ, habs⟩
  have h1 := hP D r V ψ θ μ lam ν φ hyp hsum
  have h2 := hG D r V θ hθ ν hν φ hφ habs
  have h3 : (fun β : HermE D r => IfrB V ν φ β) = fun β : HermE D r => W ψ V μ lam φ β := by
    funext β
    by_cases hβ : β.1.det = 0
    · exact hDeg D r V ψ θ μ lam ν φ hyp β hβ
    · exact hND D r V ψ θ μ lam ν φ hyp β hβ
  rw [h3] at h2
  have h4 := h1.unique h2
  have h5 := hsum.hasSum
  rwa [h4] at h5

end GlobalTheory.CompanionTheory.WeilSiegel
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_sum_invariant_levi_element : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, ⟨-, hχ⟩, -, -, -, hW⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : mat g = blk4 (a' : Matrix (Fin n) (Fin n) (AE D)) 0 0
      (adj ((a'⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) := hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact absE_inclR _
  have hc : ∀ x, (ω g Φ).1 x = Φ.1 (x * (a' : Matrix (Fin n) (Fin n) (AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))
end
