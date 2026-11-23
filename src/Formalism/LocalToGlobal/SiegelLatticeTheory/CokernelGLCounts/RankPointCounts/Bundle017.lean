module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueBackOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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

@[expose] public section

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem U_swap (f f' : Fin (r + 1) → V) :
    Submodule.span E (Set.range (Sum.elim f' f)) = Submodule.span E (Set.range (Sum.elim f f')) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem Zhat_swap (f f' : Fin (r + 1) → V) :
    H.Zhat f' f = ((M.L.cj.toRingEquiv.toRingHom).mapMatrix (H.Zhat f f'))ᵀ := by
  ext a b
  simp only [HermSp.Zhat, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact H.h_herm _ _

theorem om'_swap (f f' : Fin (r + 1) → V) : H.om' f' f = H.om f f' := by
  unfold HermSp.om' HermSp.om
  rw [Zhat_swap, ← Matrix.adjugate_transpose, ← RingHom.map_adjugate]
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem det_Zhat_swap_unit (f f' : Fin (r + 1) → V) (h : IsUnit (H.Zhat f f').det) :
    IsUnit (H.Zhat f' f).det := by
  rw [Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
  exact h.map _

theorem cond_second_of_iso (g₁ g₁' g₂ g₂' : Fin (r + 1) → V) (T₁ T₂ : F) (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H g₁ T₁)
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H g₂ T₂) (hZ₁ : IsUnit (H.Zhat g₁ g₁').det) (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂) (κ : E)
    (hz : χ (H.mkW g₁ ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩) = H.mkW g₂ ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩)
    (ho : χ (H.mkW g₁ ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩) = κ • H.mkW g₂ ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩) :
    ∀ u ∈ Submodule.span E (Set.range (Sum.elim g₁ g₁')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim g₂ g₂')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩ := by
  intro u hu hup
  obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
  let zP₁ : ↥(H.perp (H.X g₁)) := ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩
  let oP₁ : ↥(H.perp (H.X g₁)) := ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩
  let zP₂ : ↥(H.perp (H.X g₂)) := ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩
  let oP₂ : ↥(H.perp (H.X g₂)) := ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩
  have h1 : H.mkW g₁ ⟨u, hup⟩ = H.mkW g₁ (β • zP₁ + γ • oP₁) := by
    apply mkW_eq_of_sub_mem
    show u - (β • g₁ (Fin.last r) + γ • H.om' g₁ g₁') ∈ H.X g₁
    rw [hxe]
    convert hx using 1
    abel
  refine ⟨((β • zP₂ + (γ * κ) • oP₂ : ↥(H.perp (H.X g₂))) : V), ?_, (β • zP₂ + (γ * κ) • oP₂).2, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (om'_mem_U H g₂ g₂'))
  · rw [h1]
    simp only [map_add (f := _), map_smul]
    rw [show χ (H.mkW g₁ zP₁) = H.mkW g₂ zP₂ from hz, show χ (H.mkW g₁ oP₁) = κ • H.mkW g₂ oP₂ from ho, smul_smul]

end CR2

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section FG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem isNoetherianRing_locE_O' (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] :
    IsNoetherianRing L.O := by
  classical
  haveI : IsReduced E := L.reduced
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hA : ∀ a : 𝒪[F], algebraMap 𝒪[F] E a = algebraMap F E (a : F) := fun a =>
    IsScalarTower.algebraMap_apply 𝒪[F] F E a
  have hcjA : ∀ (a : F) (w : E), L.cj (algebraMap F E a * w) = algebraMap F E a * L.cj w := by
    intro a w
    rw [map_mul, L.cj.commutes]
  have hcjO : ∀ x ∈ L.O, L.cj x ∈ L.O := by
    intro x hx
    rw [L.O_def] at hx ⊢
    exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  have htr : ∀ z ∈ L.O, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = z + L.cj z := by
    intro z hz
    have hmem : z + L.cj z ∈ L.O := L.O.add_mem hz (hcjO z hz)
    obtain ⟨a, ha⟩ := (L.cj_fix (z + L.cj z)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    have hint : IsIntegral 𝒪[F] (algebraMap F E a) := ha ▸ (L.O_def _).1 hmem
    have hint' : IsIntegral 𝒪[F] a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] F E) (algebraMap F E).injective).1 hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    exact ⟨y, by rw [hA, ← ha, ← hy]; rfl⟩
  have hnd : ∀ x : E, (∀ y : E, x * y + L.cj (x * y) = 0) → x = 0 := by
    intro x hx
    have h1 : L.cj x = -x := by
      have h := hx 1
      rw [mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
    have h2 := hx x
    rw [map_mul, h1, neg_mul_neg, ← two_mul] at h2
    have hu : IsUnit (2 : E) := by
      have h3 : (2 : E) = algebraMap F E 2 := (map_ofNat (algebraMap F E) 2).symm
      rw [h3]
      exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
    have hxx : x * x = 0 := hu.mul_right_eq_zero.1 h2
    exact IsReduced.eq_zero x ⟨2, by rw [pow_two, hxx]⟩
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hsc : ∀ i, ∃ c : F, c ≠ 0 ∧ algebraMap F E c * b i ∈ L.O := by
    intro i
    haveI : Algebra.IsAlgebraic 𝒪[F] F := IsLocalization.isAlgebraic F (nonZeroDivisors 𝒪[F])
    haveI : Algebra.IsAlgebraic 𝒪[F] E := Algebra.IsAlgebraic.trans 𝒪[F] F E
    obtain ⟨c, hc, hci⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[F]) (b i)).exists_integral_multiple
    refine ⟨(c : F), by exact_mod_cast hc, (L.O_def _).2 ?_⟩
    rwa [Algebra.smul_def, hA] at hci
  choose c hc0 hcO using hsc
  let φ : 𝒪[F] →+* L.O :=
    (algebraMap 𝒪[F] E).codRestrict L.O (fun a => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hsm : ∀ (a : 𝒪[F]) (x : L.O), ((a • x : L.O) : E) = algebraMap F E (a : F) * x := by
    intro a x
    rw [Algebra.smul_def, Subring.coe_mul, ← hA]
    rfl
  let B : Fin 2 → E := fun i => algebraMap F E (c i) * b i
  let g : L.O →ₗ[𝒪[F]] (Fin 2 → E) :=
    { toFun := fun x i => (x : E) * B i + L.cj ((x : E) * B i)
      map_add' := by
        intro x y
        funext i
        simp only [Subring.coe_add, add_mul, map_add (f := _), Pi.add_apply]
        ring
      map_smul' := by
        intro a x
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [hsm, Algebra.smul_def, hA]
        simp only [mul_assoc, hcjA, mul_add] }
  let N : Submodule 𝒪[F] (Fin 2 → E) :=
    Submodule.span 𝒪[F] (Set.range fun i : Fin 2 => Pi.single i (1 : E))
  haveI : IsNoetherian 𝒪[F] N := isNoetherian_span_of_finite 𝒪[F] (Set.finite_range _)
  have hgN : ∀ x, g x ∈ N := by
    intro x
    have hx : ∀ i, ∃ a : 𝒪[F], algebraMap 𝒪[F] E a = (x : E) * B i + L.cj ((x : E) * B i) :=
      fun i => htr _ (L.O.mul_mem x.2 (hcO i))
    choose a ha using hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    show _ = fun j => (x : E) * B j + L.cj ((x : E) * B j)
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ha]
  have hinj : Function.Injective (g.codRestrict N hgN) := by
    intro x y hxy
    have h0 : g x = g y := congrArg Subtype.val hxy
    have hd : ∀ i, ((x : E) - y) * B i + L.cj (((x : E) - y) * B i) = 0 := by
      intro i
      have h := congrFun h0 i
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h
      rw [sub_mul, map_sub]
      linear_combination h
    have hb : ∀ i, ((x : E) - y) * b i + L.cj (((x : E) - y) * b i) = 0 := by
      intro i
      have h := hd i
      simp only [B] at h
      rw [mul_left_comm, hcjA, ← mul_add] at h
      exact ((IsUnit.mk0 _ (hc0 i)).map (algebraMap F E)).mul_right_eq_zero.1 h
    have hall : ∀ w, ((x : E) - y) * w + L.cj (((x : E) - y) * w) = 0 := by
      intro w
      let τ : E →ₗ[F] E := LinearMap.mulLeft F ((x : E) - y) +
        (L.cj.toLinearMap).comp (LinearMap.mulLeft F ((x : E) - y))
      have hτ : τ = 0 := b.ext (fun i => by simpa [τ] using hb i)
      simpa [τ] using LinearMap.congr_fun hτ w
    exact Subtype.ext (sub_eq_zero.1 (hnd _ hall))
  haveI : IsNoetherian 𝒪[F] L.O := isNoetherian_of_injective (g.codRestrict N hgN) hinj
  exact isNoetherianRing_iff.2 (isNoetherian_of_tower 𝒪[F] this)

theorem thFG_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThFG M r := by
  intro V _ _ H t ht
  haveI := hM.loc
  haveI := hM.char0
  haveI : IsNoetherianRing M.L.O := isNoetherianRing_locE_O' M.L
  have hfg : t.abelian₂.FG := ht.1.1.1
  haveI : IsNoetherian M.L.O t.abelian₂ := isNoetherian_of_fg_of_noetherian _ hfg
  have hle : ThL H t ≤ t.abelian₂ := inf_le_left
  haveI := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.1 inferInstance

end FG

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Tools

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

private theorem hermSp_h_sum_smul_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (c : ι → E) (x : ι → V) (y : V) : H.h (∑ i, c i • x i) y = ∑ i, c i * H.h (x i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  have h1 := map_sum φ (fun i => c i • x i) Finset.univ
  simp only [φ, AddMonoidHom.mk'_apply, H.h_smul_left] at h1
  exact h1

private theorem hermSp_h_sum_smul_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {ι : Type} [Fintype ι] (y : V) (c : ι → E) (x : ι → V) :
    H.h y (∑ i, c i • x i) = ∑ i, M.L.cj (c i) * H.h y (x i) := by

  rw [H.h_herm (∑ i, c i • x i) y, hermSp_h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← H.h_herm]

theorem gram_recomb {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type}
    [Fintype ι] (v : ι → V) (A : Matrix ι ι E) :
    H.gram (fun j => ∑ i, A i j • v i) = (A.map M.L.cj)ᵀ * H.gram v * A := by
  ext a b
  simp only [HermSp.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hermSp_h_sum_smul_left]
  simp only [hermSp_h_sum_smul_right, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem thSpan_at (M : Model F E) (r : ℕ) (hM : M.OK) : ThSpan M r := by
  intro V _ _ H t hg
  apply le_antisymm
  · exact (Submodule.span_le (R := E)).2 fun v hv => hv.2
  · intro w hw
    have hwΛ : w ∈ Submodule.span E (t.abelian₂ : Set V) := by
      rw [hg.1.1.2.1]
      exact Submodule.mem_top
    obtain ⟨c, hc0, hc⟩ := PI.LocHerm.Glue.existsIntegralMultiple M hM V t.abelian₂ w hwΛ
    have hcW : algebraMap F E (c : F) • w ∈ ThL H t := ⟨hc, Submodule.smul_mem _ _ hw⟩
    have hunit : IsUnit (algebraMap F E (c : F)) := (Units.mk0 (c : F) hc0).isUnit.map _
    have e : w = (hunit.unit⁻¹ : Eˣ) • (algebraMap F E (c : F) • w) := by
      rw [Units.smul_def, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [e, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hcW)

theorem gramMM_holds (M : Model F E) (r n : ℕ) : GramMM M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, -, -⟩ := hyp
  have hT1 := hg₁.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hI.2.2.2.2.2
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  obtain ⟨s, hs, hdet⟩ := gram_det H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂
  have hgu : IsUnit (H.gram (Sum.elim f₂ f₂')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim f₂ f₂')).det = H.Gdet f₂ f₂' t₁.T t₁.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG₂.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ f₂' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) hq0)⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
        Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) = fun j => ∑ i, A i j • Sum.elim f₂ f₂' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, smul_sub, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁, det_smul]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

end Tools

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem glue_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : Glue M r n :=
  glue_of M r n (glueFwd_of M r n hM (corrIso_holds M r n) hE)
    (glueBack_of M r n hM (corrIso_holds M r n) hE hV hP hG hFG hS) (glueInj_of M r n hM (corrIso_holds M r n))

theorem latSide_at (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) (hR : ClaimR M r n) :
    LatSide M r n :=
  latSide_of M r n (glue_at M r n hM hE hV hP hG hFG hS) hR

end Top

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_mul (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) (m n : ℤ) (y : D.host.E)
    (h : ∀ x ∈ I ^ n, x * y ∈ I ^ m) : y ∈ I ^ (m - n) := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m := by
    refine FractionalIdeal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    rw [smul_mul_assoc, mul_comm]
    exact (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))
  have h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m :=
    mul_right_mono hle
  rw [mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI,
    neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ y)

theorem coef_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V} (hv : v ∈ XS D F0)
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    y a ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a := by
    clear hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, x, hx, rfl⟩ := hx
      refine ⟨Pi.single a x, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact FractionalIdeal.zero_mem _
      · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
          Pi.single_eq_same]
    | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨y1, h1, rfl⟩ := hx
      obtain ⟨y2, h2, rfl⟩ := hw
      exact ⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a))
        ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨y1, h1, rfl⟩ := hx
      refine ⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩
      · have := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))
        rwa [Algebra.smul_def] at this
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_assoc, Algebra.smul_def]
  obtain ⟨y', hy', hv'⟩ := key
  have hyy : y = y' := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b
    exact sub_eq_zero.1 this
  rw [hyy]
  exact hy' a

end Formalism.L2.SG.Pf.ZsVolLat

end
end
