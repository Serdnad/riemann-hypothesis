module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle227
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle087
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle228
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] [StarRing K] in
theorem primInv_span_gmap (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe, ← Submodule.span_image]
  try rfl


omit [NumberField K] [StarRing K] in
theorem primInv_gmap_injective (γ : V ≃ₗ[K] V) :
    Function.Injective (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) := by
  intro M N hMN
  exact Submodule.map_injective_of_injective (f := (γ : V →ₗ[K] V).restrictScalars (𝓞 K))
    γ.injective hMN

omit [NumberField K] [StarRing K] in
theorem primInv_gmap_symm (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ M) = M := by
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change γ.symm (γ z) ∈ M
    rwa [γ.symm_apply_apply]
  · intro hx
    exact ⟨γ x, ⟨x, hx, rfl⟩, γ.symm_apply_apply x⟩

theorem primInv_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) (M : Submodule (𝓞 K) V) (hM : M ∈ PrimSubs h L j de) :
    Formalism.HermitianLatticesTheory.gmap γ M ∈ PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  obtain ⟨⟨hle, heq⟩, hrk, hdet⟩ := hM
  have hspan := primInv_span_gmap γ M
  refine ⟨⟨Submodule.map_mono hle, ?_⟩, ?_, ?_⟩
  ·
    have hres : ((Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V)).restrictScalars (𝓞 K) =
        ((Submodule.span K (M : Set V)).restrictScalars (𝓞 K)).map
          ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      ext x; exact Iff.rfl
    rw [hspan, hres]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_inf ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) γ.injective, ← heq]
  · rw [hspan, LinearEquiv.finrank_map_eq]
    exact hrk
  · rw [← hdet]
    exact GlobalTheory.T.latDetH_map_injective_isometry K V V h h (γ : V →ₗ[K] V) γ.injective (fun x y => hγ x y) M

theorem primInv_le (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) : cntPrim h L j de ≤ cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  unfold cntPrim
  rw [← Set.InjOn.encard_image (f := fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M)
    (s := PrimSubs h L j de) (fun _ _ _ _ hab => primInv_gmap_injective γ hab)]
  have hsub : (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) '' PrimSubs h L j de ⊆
      PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
    rintro _ ⟨M, hM, rfl⟩
    exact primInv_mem h γ hγ L j de M hM
  first
    | exact Set.encard_le_encard hsub
    | exact Set.encard_mono hsub
    | exact Set.encard_le_card hsub

end

theorem cntPrim_gmap_isom : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  intro K V _ _ _ _ _ _ _ h γ hγ L j de
  refine le_antisymm ?_ (primInv_le h γ hγ L j de)
  have := primInv_le h γ⁻¹ (inv_mem hγ) (Formalism.HermitianLatticesTheory.gmap γ L) j de
  rwa [primInv_gmap_symm] at this

end GlobalTheory.LoopC
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

private lemma h_add_right (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_smul_right (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

private lemma h_neg_left (H : HermSp M V) (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

private lemma h_sub_left (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

private lemma h_sub_right (H : HermSp M V) (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)
  exact map_sum φ v s

private lemma h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  let φ : V →+ E := AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)
  exact map_sum φ v s

end GlobalTheory.LocDual


open GlobalTheory.LocDual in
theorem GlobalTheory.LocDual.frameD_exists : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (f : Fin (r + 1) → V) (T : F), T ≠ 0 → (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) → H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T) → (∃ y : Fin r → V, ∀ i j : Fin r, H.h (f i.castSucc) (y j) = if i = j then 1 else 0) → ∃ Fr : FrameD H r, Fr.f = f ∧ Fr.T = T := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy
  obtain ⟨y, hy⟩ := hy
  haveI := hM.char0
  set z := f (Fin.last r) with hz
  set e : Fin r → V := fun i => f i.castSucc with he
  have hez : ∀ k, H.h (e k) z = 0 := fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  have hze : ∀ k, H.h z (e k) = 0 := fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))
  have hee : ∀ k l, H.h (e k) (e l) = 0 := fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  let y' : Fin r → V := fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z
  have hy'z : ∀ j, H.h (y' j) z = 0 := by
    intro j
    simp only [y', H.h_add_left, H.h_smul_left, hzz]
    rw [show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T
        = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]
    rw [inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]
  have hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0 := by
    intro k j
    simp only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]
    exact hy k j
  let half : E := algebraMap F E (1 / 2)
  have hhalf : M.L.cj half = half := M.L.cj.commutes _
  have hhalf2 : half + half = 1 := by
    simp only [half, ← map_add (f := _), add_halves, map_one]
  let b : Fin r → Fin r → E := fun j k => half * H.h (y' j) (y' k)
  let es : Fin r → V := fun j => y' j - ∑ k, b j k • e k
  have hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v := by
    intro i v
    simp only [es, h_sub_left, h_sum_left, H.h_smul_left]
  have hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k) := by
    intro v j
    simp only [es, h_sub_right, h_sum_right, h_smul_right]
  have hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0 := by
    intro i k
    rw [H.h_herm, hey' k i]
    split_ifs <;> simp
  refine ⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j
    rw [hesR]
    simp only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [b, map_mul, hhalf]
    rw [← H.h_herm (y' j) (y' i)]
    linear_combination (-H.h (y' i) (y' j)) * hhalf2
  · intro i j
    show H.h (e i) (es j) = _
    rw [hesR]
    simp only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro i
    show H.h (es i) z = 0
    rw [hesL]
    simp only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def gen (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

lemma cj_mem' {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hx

lemma smul_mem_lat (Λ : Submodule M.L.O V) {c : E} (hc : c ∈ M.L.O) {w : V} (hw : w ∈ Λ) :
    c • w ∈ Λ := Λ.smul_mem (⟨c, hc⟩ : M.L.O) hw

lemma h_prF_left (Fr : FrameD H r) (p s : V) (h1 : ∀ a, H.h p (Fr.e a) = 0)
    (h2 : ∀ a, H.h p (Fr.es a) = 0) : H.h (Fr.prF s) p = H.h s p := by
  rw [← hl_apply, ← hl_apply]

  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_swap_zero (h1 _),
  h_swap_zero (h2 _)]
  simp

lemma decomp (Fr : FrameD H r) (v s : V) : H.h v s = H.h (Fr.prF v) s +
    ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) s + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) s := by
  rw [← hl_apply, ← hl_apply]

  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul]
  ring

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma memL_iff (Fr : FrameD H r) (Λ : Submodule M.L.O V) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (w : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f w ∈ L ↔ ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) ∈ Λ ∧ (x : V) - w ∈ H.X Fr.f := by
  rw [← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).1 he⟩
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).2 he⟩

lemma symm_mem_gen (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (he : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (n : V ≃ₗ[E] V) (hn : IsUnitary H n)
    (hfix : ∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) (hes : ∀ a, n (Fr.es a) ∈ Λ)
    (hX : ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) {u : V} (hu : u ∈ Λ) :
    n.symm u ∈ gen Fr L := by
  set v := n.symm u with hv
  have hnv : n v = u := by simp [hv]
  have hve : ∀ a, H.h v (Fr.e a) = H.h u (Fr.e a) := fun a => by
    rw [← hn v (Fr.e a), hnv]; exact congrArg _ (hfix a)
  have hveO : ∀ a, H.h v (Fr.e a) ∈ M.L.O := fun a => by
    rw [hve]; exact (hSD.2.2 u).1 hu _ (he a)
  have hvesO : ∀ a, H.h v (Fr.es a) ∈ M.L.O := fun a => by
    rw [← hn v (Fr.es a), hnv]; exact (hSD.2.2 u).1 hu _ (hes a)
  refine ⟨hvesO, hveO, ⟨Fr.prF v, prF_perp Fr v⟩, rfl, ?_⟩
  set v' := v - ∑ a, H.h v (Fr.e a) • Fr.es a with hv'
  have hv'p : v' ∈ H.perp (H.X Fr.f) := by
    rw [mem_perpX]
    intro b
    rw [← hl_apply]

    simp only [hv', map_sub, map_sum, map_smul, hl_apply, h_es_e, smul_eq_mul]
    simp
  have hx : n v' = u - ∑ a, H.h v (Fr.e a) • n (Fr.es a) := by

    simp [hv', map_sub, map_sum, hnv]
  have hxΛ : n v' ∈ Λ := by
    rw [hx]
    exact Λ.sub_mem hu (Λ.sum_mem fun a _ => smul_mem_lat Λ (hveO a) (hes a))
  have hxv' := hX v' hv'p
  have hxp : n v' ∈ H.perp (H.X Fr.f) := by
    have := (H.perp (H.X Fr.f)).add_mem hv'p (X_le_perp Fr hxv')
    simpa using this
  rw [memL_iff Fr Λ L hL]
  refine ⟨⟨n v', hxp⟩, hxΛ, ?_⟩
  have hpr : Fr.prF v - v' = -∑ a, H.h v (Fr.es a) • Fr.e a := by
    simp only [FrameD.prF, hv']; abel
  have : (n v' : V) - Fr.prF v = (n v' - v') - (Fr.prF v - v') := by abel
  show n v' - Fr.prF v ∈ H.X Fr.f
  rw [this, hpr]
  exact (H.X Fr.f).sub_mem hxv' ((H.X Fr.f).neg_mem
    ((H.X Fr.f).sum_mem fun a _ => (H.X Fr.f).smul_mem _ (e_mem_X Fr a)))

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma h_gen_mem (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f)
    {v s : V} (hv : v ∈ gen Fr L) (hs : s ∈ gen Fr L) : H.h v s ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hs1, hs2, ws, hws, hwsL⟩ := hs
  obtain ⟨x, hxΛ, hxd⟩ := (memL_iff Fr Λ L hL wv).1 hwvL
  obtain ⟨x', hx'Λ, hx'd⟩ := (memL_iff Fr Λ L hL ws).1 hwsL
  rw [hwv] at hxd
  rw [hws] at hx'd

  have hpp : H.h (Fr.prF v) (Fr.prF s) = H.h (x : V) (x' : V) := by
    have e1 : Fr.prF v = x - ((x : V) - Fr.prF v) := by abel
    have e2 : Fr.prF s = x' - ((x' : V) - Fr.prF s) := by abel
    have k1 : H.h ((x : V) - Fr.prF v) (Fr.prF s) = 0 :=
      h_swap_zero (prF_perp Fr s _ hxd)
    have k2 : H.h (x : V) ((x' : V) - Fr.prF s) = 0 := x.2 _ hx'd
    calc H.h (Fr.prF v) (Fr.prF s)
        = H.h (x : V) (Fr.prF s) - H.h ((x : V) - Fr.prF v) (Fr.prF s) := by
          rw [← hl_apply, ← hl_apply, ← hl_apply, ← map_sub, ← e1]
      _ = H.h (x : V) (Fr.prF s) := by rw [k1, sub_zero]
      _ = H.h (x : V) (x' : V) := by
          rw [e2, ← neg_add_eq_sub, h_add_right, ← neg_one_smul E ((x' : V) - Fr.prF s),
            h_smul_right, k2, mul_zero, zero_add]
  have hpO : H.h (Fr.prF v) s ∈ M.L.O := by
    have e3 : H.h (Fr.prF v) s = M.L.cj (H.h s (Fr.prF v)) := H.h_herm _ _
    rw [e3, ← h_prF_left Fr (Fr.prF v) s (h_prF_e Fr v) (h_prF_es Fr v), H.h_herm, M.L.cj_cj, hpp]
    exact (hSD.2.2 x).1 hxΛ _ hx'Λ
  rw [decomp Fr v s]
  refine M.L.O.add_mem (M.L.O.add_mem hpO ?_) ?_
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv1 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs2 a)
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv2 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs1 a)

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr Λ hSD he L hL n hn hfix hes hX
  have hb := fun {u : V} (hu : u ∈ Λ) => symm_mem_gen Fr Λ hSD he L hL n hn hfix hes hX hu
  have hgen : FrameD.LamStd Fr L = Submodule.span M.L.O (gen Fr L) := rfl
  apply le_antisymm
  · intro u hu
    rw [hgen]
    exact ⟨n.symm u, Submodule.subset_span (hb hu), by simp⟩
  · rw [hgen, img, Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro s hs
    show n s ∈ Λ
    refine (hSD.2.2 (n s)).2 fun t ht => ?_
    have ht' : n (n.symm t) = t := by simp
    rw [← ht', hn]
    exact h_gen_mem Fr Λ hSD L hL hs (hb ht)

end GlobalTheory.StdLatImg
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.IotaDense

theorem iota_dense : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O,
    c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  obtain ⟨hR, -, -, -, hO, -, -, -, hunit, hcl⟩ := GlobalTheory.LocAtTopology.locAt_topology D.sp.cm D.conjF
    (fun x => by rw [D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]) p (D.s.atP p)
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : gS D ≠ 0 := by
      unfold gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hunit _ hg
  set S : Set (D.s.atP p).Ep := (fun z => ((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - z)) ⁻¹' ((D.s.atP p).O : Set _)
    with hSdef
  have hSo : IsOpen S := hO.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hcS : c ∈ S := by
    show _ * (c - c) ∈ (D.s.atP p).O
    rw [sub_self, mul_zero]; exact zero_mem _
  have hcc : c ∈ closure (Set.range fun x : 𝓞 D.host.E => (D.s.atP p).ιE (x : D.host.E)) := by
    rw [hcl]; exact hc
  obtain ⟨z, hzS, a, rfl⟩ := mem_closure_iff.1 hcc S hSo hcS
  refine ⟨a, _, hzS, ?_⟩
  show c = _ + _ * (((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - _))
  rw [← hw, ← mul_assoc, Units.mul_inv, one_mul]
  ring

end GlobalTheory.IotaDense
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  first | exact @GlobalTheory.lintegral_prod_pow_le_of_moments | exact GlobalTheory.lintegral_prod_pow_le_of_moments | (intros; apply GlobalTheory.lintegral_prod_pow_le_of_moments <;> assumption)
end
