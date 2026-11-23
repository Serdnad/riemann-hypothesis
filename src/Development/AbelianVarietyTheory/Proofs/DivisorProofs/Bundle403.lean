module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle347
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}

theorem invariant_comp_mulVec [Fintype κ] [DecidableEq κ] (m : ((κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hm : ∀ φ ∈ SB (κ → F), ∀ a, m (fun x => φ (x + a)) = m φ) (g : GL κ F) {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F))
    (hφ' : (fun x => φ (g.val.mulVec x)) ∈ SB (κ → F)) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * m (fun x => φ (g.val.mulVec x)) = m φ := by
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  have := nonarch_pi F κ
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → F) (Measure.pi fun _ => (Measure.addHaar : Measure F)) m hm
  rw [hc _ hφ, hc _ hφ', mul_left_comm, integral_comp_mulVec]

theorem diag_mem_SB [Fintype κ] {φ : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) :
    (fun x : κ → F => φ (Sum.elim x x)) ∈ SB (κ → F) := by
  have := SplitWeil.t2Space F
  have hc : Continuous fun x : κ → F => (Sum.elim x x : κ ⊕ κ → F) :=
    continuous_pi (by rintro (k | k) <;> exact continuous_apply k)
  have hc' : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  refine ⟨hφ.1.comp_continuous hc, HasCompactSupport.intro (hφ.2.image hc') fun x hx => ?_⟩
  by_contra h
  exact hx ⟨Sum.elim x x, subset_tsupport _ h, rfl⟩

theorem diag_invariant_comp [Invertible (2 : F)] [Fintype κ] [DecidableEq κ] (ψ : AddChar F ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → F, ∀ φ ∈ SB (κ ⊕ κ → F), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (g : GL κ F) {φ φ' : (κ ⊕ κ → F) → ℂ} (hφ : φ ∈ SB (κ ⊕ κ → F)) (hφ' : φ' ∈ SB (κ ⊕ κ → F))
    (h : ∀ x, φ' (Sum.elim x x) = φ (Sum.elim (g.val.mulVec x) (g.val.mulVec x))) :
    ((distribHaarChar F (GeneralLinearGroup.det g) : ℝ) : ℂ) * l φ' = l φ := by
  classical
  have := SplitWeil.t2Space F
  have := nonarch_field F
  have hlc := isLocallyConstant_addChar ψ hψ

  have hz : ∀ φ ∈ SB (κ ⊕ κ → F), (∀ x, φ (Sum.elim x x) = 0) → l φ = 0 := by
    intro φ hφ h0
    refine eq_zero_of_mul_invariant l (Set.range fun y : κ → F => fun u => ψ (u ⬝ᵥ Sum.elim y (-y))) ?_ ?_ hφ ?_
    · rintro _ ⟨y, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, rfl⟩ φ hφ
      rw [← hl 0 y φ hφ]
      congr 1
      funext u
      simp [schr]
    · intro u hu
      obtain ⟨k, hk⟩ : ∃ k, u (Sum.inl k) - u (Sum.inr k) ≠ 0 := by
        by_contra hne
        push Not at hne
        apply hu
        rw [← h0 (u ∘ Sum.inl)]
        congr 1
        ext (k | k)
        · rfl
        · exact (sub_eq_zero.mp (hne k)).symm
      obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ1
      refine ⟨_, ⟨Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))), rfl⟩, ?_⟩
      have : u ⬝ᵥ Sum.elim (Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k))))
          (-Pi.single k (a / (u (Sum.inl k) - u (Sum.inr k)))) = a := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr u]
        rw [sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_single, dotProduct_single, ← sub_eq_add_neg,
          ← sub_mul]
        exact mul_div_cancel₀ _ hk
      show ψ _ ≠ 1
      rwa [this]

  let K : Set (κ → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int F
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int F⟩
  let e : (κ → F) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → F) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → F) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → F) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → F => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → F), ext f ∈ SB (κ ⊕ κ → F) := by
    intro f hf
    have c3 : Continuous fun p : (κ → F) × (κ → F) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → F) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → F), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply, ← sub_eq_zero, ← map_sub]
    refine hz _ (sub_mem hφ (hSB _ (diag_mem_SB hφ))) fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → F), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  have h' := diag_mem_SB hφ'
  rw [hres φ hφ, hres φ' hφ']
  simp only [h] at h' ⊢
  exact invariant_comp_mulVec _ hinv g (diag_mem_SB hφ) h'

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

section Pair

variable {R : Type} [CommRing R]



end Pair

end GlobalTheory.WeilM

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  first | exact @GlobalTheory.EtC.sec_sep_glue_of_points | exact GlobalTheory.EtC.sec_sep_glue_of_points | (intros; apply GlobalTheory.EtC.sec_sep_glue_of_points <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], (∀ ζ : Prim q A, ζ.1 ^ q = 1) ∧ (∀ (ζ : Prim q A) (a : ℕ), Nat.Coprime a q → ∃ ξ : Prim q A, ξ.1 = ζ.1 ^ a) ∧ (∀ (ζ : Prim q A) (a b : ℕ), ¬ a ≡ b [MOD q] → IsUnit (ζ.1 ^ a - ζ.1 ^ b)) ∧ (∀ (ζ : Prim q A) (x : A), x ^ q = 1 → ∏ a ∈ Finset.range q, (x - ζ.1 ^ a) = 0) ∧ (∀ (ζ ξ : Prim q A), ∏ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (ξ.1 - ζ.1 ^ a) = 0) ∧ ∀ (r : ℕ), r ∣ q → ∀ ζ : Prim q A, ∃ ξ : Prim r A, ξ.1 = ζ.1 ^ (q / r) := by
  first | (exact @GlobalTheory.EtC.PrimBasic.prim_basic) | (exact GlobalTheory.EtC.PrimBasic.prim_basic) | (intros; apply GlobalTheory.EtC.PrimBasic.prim_basic  <;> assumption)
end

section

open CategoryTheory GlobalTheory.CxCoh

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxCoh.Collapse

theorem bij_of_two {A B X Y : Type*} (r : A → B) (w : B → X) (s : X → Y) (U : A → X) (E : B → Y)
    (hU : ∀ x, U x = w (r x)) (hE : ∀ y, E y = s (w y))
    (bU : Function.Bijective U) (bE : Function.Bijective E) : Function.Bijective r := by
  have wi : Function.Injective w := fun y y' h ↦ bE.1 (by rw [hE, hE, h])
  refine ⟨fun x x' h ↦ bU.1 (by rw [hU, hU, h]), fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := bU.2 (w y)
  exact ⟨x, wi (by rw [← hU, hx])⟩

variable {C : Type 1} [Category.{0} C] {D : Type} [Category.{0} D]

def uMap (K : Cx C) (S : C ⥤ C) (u : 𝟭 C ⟶ S) : CxMap K (K.res S) where
  G := 𝟭 C
  a0 T := K.M0.map (u.app T)
  a1 T := K.M1.map (u.app T)
  a2 T := K.M2.map (u.app T)
  a3 T := K.M3.map (u.app T)
  compDegreeZero_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M0.map_comp, ← K.M0.map_comp, h]
  compDegreeOne_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M1.map_comp, ← K.M1.map_comp, h]
  compDegreeTwo_natural φ x := by
    have h := u.naturality φ
    simp only [Functor.id_map] at h ⊢
    rw [← K.M2.map_comp, ← K.M2.map_comp, h]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def wMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) : CxMap (K.res ℓ) (K.res S) where
  G := q
  a0 T := K.M0.map (w.app T)
  a1 T := K.M1.map (w.app T)
  a2 T := K.M2.map (w.app T)
  a3 T := K.M3.map (w.app T)
  compDegreeZero_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M0.map (w.app T') (K.M0.map (ℓ.map (q.map φ)) x) = K.M0.map (S.map φ) (K.M0.map (w.app T) x)
    rw [← K.M0.map_comp, ← K.M0.map_comp, this]
  compDegreeOne_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M1.map (w.app T') (K.M1.map (ℓ.map (q.map φ)) x) = K.M1.map (S.map φ) (K.M1.map (w.app T) x)
    rw [← K.M1.map_comp, ← K.M1.map_comp, this]
  compDegreeTwo_natural {T T'} φ x := by
    have := w.naturality φ
    simp only [Functor.comp_map] at this
    change K.M2.map (w.app T') (K.M2.map (ℓ.map (q.map φ)) x) = K.M2.map (S.map φ) (K.M2.map (w.app T) x)
    rw [← K.M2.map_comp, ← K.M2.map_comp, this]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

def eMap (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q) :
    CxMap (K.res ℓ) ((K.res S).res ℓ) where
  G := 𝟭 D
  a0 T := K.M0.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a1 T := K.M1.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a2 T := K.M2.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  a3 T := K.M3.map (ℓ.map (ε.app T) ≫ w.app (ℓ.obj T))
  compDegreeZero_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M0.map _ (K.M0.map (ℓ.map φ) x) = K.M0.map (S.map (ℓ.map φ)) (K.M0.map _ x)
    rw [← K.M0.map_comp, ← K.M0.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeOne_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M1.map _ (K.M1.map (ℓ.map φ) x) = K.M1.map (S.map (ℓ.map φ)) (K.M1.map _ x)
    rw [← K.M1.map_comp, ← K.M1.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  compDegreeTwo_natural {T T'} φ x := by
    have h1 := ε.naturality φ
    have h2 := w.naturality (ℓ.map φ)
    simp only [Functor.comp_map, Functor.id_map] at h1 h2
    change K.M2.map _ (K.M2.map (ℓ.map φ) x) = K.M2.map (S.map (ℓ.map φ)) (K.M2.map _ x)
    rw [← K.M2.map_comp, ← K.M2.map_comp]
    congr 1
    rw [← Category.assoc, ← ℓ.map_comp, h1, ℓ.map_comp, Category.assoc, h2, Category.assoc]
  comp_commutes_diffZero T x := (K.diffZero_natural _ x).symm
  comp_commutes_diffOne T x := (K.diffOne_natural _ x).symm
  comp_commutes_diffTwo T x := (K.diffTwo_natural _ x).symm

end GlobalTheory.CxCoh.Collapse


open GlobalTheory.CxCoh.Collapse in
theorem GlobalTheory.CxCoh.collapse_resMap_bij : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (ℓ : D ⥤ C)
    (q : C ⥤ D) (S : C ⥤ C) (u : 𝟭 C ⟶ S) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q), (∀ T, K.QAt (u.app T)) →
    (∀ U, K.QAt (ℓ.map (ε.app U) ≫ w.app (ℓ.obj U))) → (K.resMap ℓ).Bij := by
  intro C _ D _ K ℓ q S u w ε hu hε
  let U := uMap K S u
  let W := wMap K ℓ q S w
  let E := eMap K ℓ q S w ε
  have jU : U.Joined (K.resMap S) u := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jW : ((K.resMap ℓ).comp W).Joined (K.resMap S) w := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have jE : E.Joined (W.comp ((K.res S).resMap ℓ)) ε :=
    ⟨fun _ x ↦ (K.M0.map_comp _ _ x).symm, fun _ x ↦ (K.M1.map_comp _ _ x).symm,
      fun _ x ↦ (K.M2.map_comp _ _ x).symm⟩
  have qU : U.QAll := hu
  have qE : E.QAll := hε
  have a0U := GlobalTheory.T.vertical_h0_bijective_h1_injective_universes.1 U qU
  have a1U := GlobalTheory.T.vertical_h1_surjective_universes.1 U qU
  have a2U := GlobalTheory.T.vertical_h2_injective_three_universe_pairs.1 U qU
  have a3U := GlobalTheory.T.vertical_h2_surjective_universes.1 U qU
  have a0E := GlobalTheory.T.vertical_h0_bijective_h1_injective_universes.2.2 E qE
  have a1E := GlobalTheory.T.vertical_h1_surjective_universes.2.2 E qE
  have a2E := GlobalTheory.T.vertical_h2_injective_three_universe_pairs.2.2 E qE
  have a3E := GlobalTheory.T.vertical_h2_surjective_universes.2.2 E qE
  have oU := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jU
  have oW := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.1 _ _ _ jW
  have oE := GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances.2.2 _ _ _ jE
  have tU := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.1 _ _ _ jU
  have tW := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.1 _ _ _ jW
  have tE := GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances.2.2 _ _ _ jE
  refine ⟨bij_of_two _ W.h0 ((K.res S).resMap ℓ).h0 U.h0 E.h0 (fun x ↦ ?_) (fun y ↦ ?_) a0U.1 a0E.1,
    bij_of_two _ W.h1 ((K.res S).resMap ℓ).h1 U.h1 E.h1 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a0U.2, a1U⟩ ⟨a0E.2, a1E⟩,
    bij_of_two _ W.h2 ((K.res S).resMap ℓ).h2 U.h2 E.h2 (fun x ↦ ?_) (fun y ↦ ?_) ⟨a2U, a3U⟩ ⟨a2E, a3E⟩⟩
  · rw [oU.1, ← oW.1, CxMap.cohomZero_pullback_comp]
  · rw [oE.1, CxMap.cohomZero_pullback_comp]
  · rw [oU.2, ← oW.2, CxMap.cohomOne_pullback_comp]
  · rw [oE.2, CxMap.cohomOne_pullback_comp]
  · rw [tU, ← tW, CxMap.cohomTwo_pullback_comp]
  · rw [tE, CxMap.cohomTwo_pullback_comp]
end
end

section

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def twistSpan (ν β : kˣ →* ℂˣ) : Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {z | ∃ (g : GL A k) (Ψ : Matrix A D k → ℂ), Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧
    z = omA ν β g 1 Ψ - Ψ}

def lowRank (r : ℕ) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0}
  add_mem' hΦ hΨ := ⟨add_mem hΦ.1 hΨ.1, fun Y hY => by simp [hΦ.2 Y hY, hΨ.2 Y hY]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ hΦ := ⟨Submodule.smul_mem _ c hΦ.1, fun Y hY => by simp [hΦ.2 Y hY]⟩

theorem mem_lowRank {r : ℕ} {Φ : Matrix A D k → ℂ} :
    Φ ∈ lowRank r ↔ Φ ∈ GlobalTheory.WeilM.SB (Matrix A D k) ∧ ∀ Y : Matrix A D k, Y.rank < r → Φ Y = 0 := Iff.rfl

theorem omA_one_apply (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) (X : Matrix A D k) :
    omA ν β g 1 Φ X = (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
      Φ ((g⁻¹).val * X) := by
  simp [omA, invT_val]

theorem sub_mem_twistSpan (ν β : kˣ →* ℂˣ) (g : GL A k) {Ψ : Matrix A D k → ℂ}
    (hΨ : Ψ ∈ GlobalTheory.WeilM.SB (Matrix A D k)) : omA ν β g 1 Ψ - Ψ ∈ twistSpan ν β :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

def box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Set (Matrix A D k) :=
  {X | ∀ i j, valuation k (X i j - C i j) ≤ valuation k ((ϖ ^ e i : kˣ) : k)}

def boxFn (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : Matrix A D k → ℂ := (box ϖ C e).indicator 1


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_preimage (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ e i)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [box, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ e i : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_image (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    box ϖ C e = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ e i : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [box_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY


omit [DecidableEq A] [DecidableEq D] in
theorem isCompact_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsCompact (box ϖ C e) := by
  rw [box_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem isClopen_box (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) : IsClopen (box ϖ C e) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_box ϖ C e).isClosed, ?_⟩
  rw [box_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)


omit [DecidableEq A] [DecidableEq D] in
theorem boxFn_mem_SB (ϖ : kˣ) (C : Matrix A D k) (e : A → ℕ) :
    boxFn ϖ C e ∈ GlobalTheory.WeilM.SB (Matrix A D k) :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_box ϖ C e)).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box ϖ C e) fun _ hx => Set.indicator_of_notMem hx _⟩


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem box_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) : box ϖ X e = box ϖ C e := by
  ext Y
  refine ⟨fun hY i j => ?_, fun hY i j => ?_⟩
  · rw [show Y i j - C i j = (Y i j - X i j) + (X i j - C i j) by ring]
    exact Valuation.map_add_le _ (hY i j) (hX i j)
  · rw [show Y i j - X i j = (Y i j - C i j) - (X i j - C i j) by ring]
    exact Valuation.map_sub_le _ (hY i j) (hX i j)


omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem boxFn_eq_of_mem {ϖ : kˣ} {C X : Matrix A D k} {e : A → ℕ} (hX : X ∈ box ϖ C e) :
    boxFn ϖ X e = boxFn ϖ C e := by
  rw [boxFn, boxFn, box_eq_of_mem hX]

end GlobalTheory.RankCoinv
end
end

section

open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Nsp (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {Z | ∃ g : GL A k, ∃ Ψ' ∈ SB (Matrix A D k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}

variable {k}

theorem Nsp_le_SB (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, Ψ', hΨ', rfl⟩
  exact Submodule.sub_mem _ (GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 hΨ') hΨ'

theorem sub_mem_Nsp {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

end GlobalTheory.RankStrata
end
end
