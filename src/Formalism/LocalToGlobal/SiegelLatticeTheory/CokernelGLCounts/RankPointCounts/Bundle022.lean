module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGram
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.IsOpenAddSubgroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
      | (simp only [hF, hF']; rfl)
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section GP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem prim_comp {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {Λ : Submodule M.L.O V} {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {v : ι → V} (hv : H.Prim Λ v)
    (e : κ → ι) (he : Function.Injective e) : H.Prim Λ (v ∘ e) := by
  refine ⟨fun a => hv.1 (e a), hv.2.1.comp e he, fun x hx hxs => ?_⟩
  have hxv : x ∈ Submodule.span E (Set.range v) := Submodule.span_mono (Set.range_comp_subset_range e v) hxs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hv.2.2 x hx hxv)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have ha' : ∑ i, ((a i : M.L.O) : E) • v i = x := ha
  let d' : ι → E := fun i => ∑ j, if e j = i then d j else 0
  have hd' : ∑ i, d' i • v i = ∑ j, d j • v (e j) := by
    simp only [d', Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_ite_eq]
    simp
  have hcoef : ∀ i, ((a i : M.L.O) : E) = d' i := by
    have h0 : ∑ i, (((a i : M.L.O) : E) - d' i) • v i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [hd', ha']
      simpa using hd.symm ▸ sub_self x
    intro i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hv.2.1 _ h0 i)
  have hzero : ∀ i, i ∉ Set.range e → a i = 0 := by
    intro i hi
    apply Subtype.ext
    rw [hcoef i]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (fun h => hi ⟨j, h⟩)]
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => a (e j), ?_⟩
  rw [← ha]
  exact (Fintype.sum_of_injective e he (fun j => a (e j) • (v ∘ e) j) (fun i => a i • v i)
    (fun i hi => by rw [hzero i hi, zero_smul]) (fun j => rfl))

theorem genOfPrim_holds (M : Model F E) (r n : ℕ) : GenOfPrim M r n := by
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂ Λ₂ hsd hprim
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
  have hnt : Nontrivial E := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    have h0 := Module.finrank_zero_of_subsingleton (R := F) (M := E)
    rw [M.L.rank] at h0
    exact absurd h0 (by norm_num)
  have hfam_inl : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inl = f₂ := by
    funext a
    unfold HermSp.MMfam
    rcases M.split with _ | g <;> rfl
  have hPf : H.Prim Λ₂ f₂ := by
    have := prim_comp H hprim Sum.inl Sum.inl_injective
    rwa [hfam_inl] at this
  have hPf' : H.Prim Λ₂ f₂' := by
    rcases hs : M.split with _ | g
    · have hfam_inr : (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r)) ∘ Sum.inr = f₂' := by
        funext a
        unfold HermSp.MMfam
        rw [hs]
        rfl
      have := prim_comp H hprim Sum.inr Sum.inr_injective
      rwa [hfam_inr] at this
    · set Q : E := algebraMap F E (g.q : F)
      set qi : E := algebraMap F E ((g.q : F)⁻¹)
      have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
      have hQqi : Q * qi = 1 := by
        simp only [Q, qi]
        rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
      have hQO : Q ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
      have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) = Sum.elim f₂ (fun a => qi • (f₂' a - f₂ a)) := by
        unfold HermSp.MMfam
        rw [hs]
      rw [hMM] at hprim
      obtain ⟨hmem, hli, hsat⟩ := hprim
      set y : Fin (r + 1) → V := fun a => qi • (f₂' a - f₂ a)
      have hf' : ∀ a, f₂' a = f₂ a + Q • y a := by
        intro a
        simp only [y]
        rw [smul_smul, hQqi, one_smul]
        abel
      refine ⟨fun a => ?_, ?_, fun x hx hxs => ?_⟩
      · rw [hf' a]
        refine Submodule.add_mem _ (hmem (Sum.inl a)) ?_
        have := Λ₂.smul_mem (⟨Q, hQO⟩ : M.L.O) (hmem (Sum.inr a))
        rwa [Subring.smul_def] at this
      · rw [Fintype.linearIndependent_iff]
        intro d hd a
        have h0 : ∑ i, (Sum.elim d (fun b => d b * Q) i) • Sum.elim f₂ y i = 0 := by
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          rw [← hd, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hf' b, smul_add, mul_smul]
        exact (Fintype.linearIndependent_iff.1 hli) _ h0 (Sum.inl a)
      · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
        have hx2 : ∑ a, d a • f₂' a ∈ Submodule.span E (Set.range (Sum.elim f₂ y)) := by
          refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
          rw [hf' a]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩))
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hsat _ hx hx2)
        have hcoef := (Fintype.linearIndependent_iff.1 hli)
          (fun i => (c i : E) - Sum.elim d (fun b => d b * Q) i) (by
            simp only [sub_smul, Finset.sum_sub_distrib]
            have e1 : ∑ i, (c i : E) • Sum.elim f₂ y i = ∑ a, d a • f₂' a := by
              rw [← hc]
              exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
            rw [e1, Fintype.sum_sum_type]
            simp only [Sum.elim_inl, Sum.elim_inr]
            rw [← Finset.sum_add_distrib, sub_eq_zero]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hf' b, smul_add, mul_smul])
        have hdO : ∀ a, d a ∈ M.L.O := by
          intro a
          have := hcoef (Sum.inl a)
          simp only [Sum.elim_inl] at this
          rw [← sub_eq_zero.1 this]
          exact (c _).2
        refine Submodule.sum_mem _ fun a _ => ?_
        have := Submodule.smul_mem (Submodule.span M.L.O (Set.range f₂')) (⟨d a, hdO a⟩ : M.L.O)
          (Submodule.subset_span ⟨a, rfl⟩)
        rwa [Subring.smul_def] at this
  refine ⟨⟨hsd, ⟨hPf, hF₂.1, hF₂.2, hT1.2.1.2.2.2⟩, ⟨hPf', hF₂'.1, hF₂'.2, hT1.2.2.1.2.2.2⟩, hD₂, hG₂.ne_zero,
    fun g hs => ⟨(hT1.2.2.2.2.2 g hs).1, (hT1.2.2.2.2.2 g hs).2.1, fun b => ?_⟩⟩, hprim⟩
  have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hMM : H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) =
      Sum.elim f₂ (fun a => algebraMap F E ((g.q : F)⁻¹) • (f₂' a - f₂ a)) := by
    unfold HermSp.MMfam
    rw [hs]
  have hy : algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b) ∈ Λ₂ := by
    have := hprim.1 (Sum.inr b)
    rw [hMM] at this
    exact this
  have e : f₂' b - f₂ b = algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (f₂' b - f₂ b)) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul]
  show f₂' b - f₂ b ∈ H.smulLat (algebraMap F E (g.q : F)) Λ₂
  rw [e]
  exact Submodule.subset_span ⟨_, hy, rfl⟩

end GP

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ProdEP2Uni

section LocTop

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem topE (M : Loc.Model F E) : IsTopologicalRing E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  first
    | exact IsModuleTopology.isTopologicalRing F E
    | exact IsModuleTopology.topologicalRing F E

theorem t2E (M : Loc.Model F E) : T2Space E := by
  haveI := M.L.top
  haveI := M.L.free
  haveI : T2Space F := MainNotions.LocalModelPeriodLattices.nonarchimedean_local_field_t2 inferInstance
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  let b := Module.Free.chooseBasis F E
  have hc : Continuous (b.equivFun : E → (Module.Free.ChooseBasisIndex F E → F)) :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  exact T2Space.of_injective_continuous b.equivFun.injective hc

theorem int_mem {x : F} (h : IsIntegral 𝒪[F] x) : x ∈ 𝒪[F] := by
  first
    | exact (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
    | (obtain ⟨y, hy⟩ := (Valuation.integer.integers (ValuativeRel.valuation F)).mem_of_integral h
       rw [← hy]
       exact y.2)

theorem alg_int (x : 𝒪[F]) : algebraMap F E (x : F) = algebraMap 𝒪[F] E x := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply 𝒪[F] F E x).symm

private theorem R_eq_O_of_split_eq_none (M : Loc.Model F E) (hg : M.split = none) : M.R = M.L.O := by
  simp only [Loc.Model.R, hg]

private theorem mem_R_iff_of_split_eq_some (M : Loc.Model F E) (g : Loc.SplitG M.L) (hg : M.split = some g) (z : E) :
    z ∈ M.R ↔ ∃ a b : 𝒪[F], g.e z = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  simp only [Loc.Model.R, hg, Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, RingHom.mem_eqLocus.mp hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), RingHom.mem_eqLocus.mpr hab, he.symm⟩

theorem alg_mem_R (M : Loc.Model F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ M.R := by
  cases hg : M.split with
  | none =>
    rw [R_eq_O_of_split_eq_none M hg, M.L.O_def, alg_int]
    exact isIntegral_algebraMap
  | some g =>
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨a, a, ?_, rfl⟩
    rw [AlgEquiv.commutes]
    first
      | rfl
      | simp

private theorem splitG_e_mem_integers_of_mem_O (L : Loc.LocE F E) (g : Loc.SplitG L) {z : E} (hz : z ∈ L.O) :
    (g.e z).1 ∈ 𝒪[F] ∧ (g.e z).2 ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (g.e z) := ((L.O_def z).mp hz).map (g.e.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨int_mem (h1.map ((AlgHom.fst F F F).restrictScalars 𝒪[F])),
    int_mem (h1.map ((AlgHom.snd F F F).restrictScalars 𝒪[F]))⟩

private theorem mem_O_of_mem_R (M : Loc.Model F E) {z : E} (hz : z ∈ M.R) : z ∈ M.L.O := by
  cases hg : M.split with
  | none =>
    rwa [R_eq_O_of_split_eq_none M hg] at hz
  | some g =>
    obtain ⟨a, b, he, -⟩ := (mem_R_iff_of_split_eq_some M g hg z).mp hz
    rw [M.L.O_def]
    have ha : IsIntegral 𝒪[F] (a : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F a))
    have hb : IsIntegral 𝒪[F] (b : F) := (isIntegral_algebraMap : IsIntegral 𝒪[F] (algebraMap 𝒪[F] F b))
    have h1 : IsIntegral 𝒪[F] (((a : F), (b : F)) : F × F) := IsIntegral.pair ha hb
    have h2 := h1.map (g.e.symm.toAlgHom.restrictScalars 𝒪[F])
    rw [← he] at h2
    have e : (g.e.symm.toAlgHom.restrictScalars 𝒪[F]) (g.e z) = z := g.e.symm_apply_apply z
    rwa [e] at h2

theorem R_compact [CharZero F] (M : Loc.Model F E) : IsCompact (M.R : Set E) := by
  haveI := topE M
  have hO := (MainNotions.LocalModelPeriodLattices.O_top M.L).2.1
  have hRo : IsOpen (M.R : Set E) := PI.ProdFormulaE.ROpen.isOpen_R M
  have hRc : IsClosed (M.R : Set E) := M.R.toAddSubgroup.isClosed_of_isOpen hRo
  exact hO.of_isClosed_subset hRc (fun z hz => mem_O_of_mem_R M hz)

theorem R_denom (M : Loc.Model F E) (y : E) : ∃ a : 𝒪[F], a ≠ 0 ∧ algebraMap F E (a : F) * y ∈ M.R := by
  haveI := M.L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  haveI : Nontrivial E := by
    first
      | exact Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
      | exact Module.nontrivial_of_finrank_eq_succ M.L.rank
  haveI : IsFractionRing 𝒪[F] F := ValuationRing.instIsFractionRingInteger (ValuativeRel.valuation F)
  have hinj : ∀ x : 𝒪[F], algebraMap 𝒪[F] E x = 0 → x = 0 := by
    intro x hx
    rw [← alg_int] at hx
    exact Subtype.ext ((map_eq_zero_iff _ (algebraMap F E).injective).mp hx)
  have halg : IsAlgebraic 𝒪[F] y := by
    have hF : IsAlgebraic F y := (Algebra.IsIntegral.isIntegral (R := F) y).isAlgebraic
    exact (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr hF
  have hex : ∃ s : 𝒪[F], s ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E s * y) := by
    first
      | (obtain ⟨z, s, hs, hz⟩ := exists_integral_multiple halg hinj
         exact ⟨s, hs, by rw [mul_comm, hz]; exact z.2⟩)
      | (obtain ⟨s, hs, hi⟩ := halg.exists_integral_multiple
         exact ⟨s, hs, by rwa [Algebra.smul_def] at hi⟩)
  obtain ⟨s, hs, hsi⟩ := hex
  have hsy : algebraMap F E (s : F) * y ∈ M.L.O := by
    rw [M.L.O_def, alg_int]
    exact hsi
  cases hg : M.split with
  | none =>
    exact ⟨s, hs, by rw [R_eq_O_of_split_eq_none M hg]; exact hsy⟩
  | some g =>
    refine ⟨g.q * s, mul_ne_zero g.q_irr.ne_zero hs, ?_⟩
    obtain ⟨h1, h2⟩ := splitG_e_mem_integers_of_mem_O M.L g hsy
    rw [mem_R_iff_of_split_eq_some M g hg]
    refine ⟨g.q * ⟨_, h1⟩, g.q * ⟨_, h2⟩, ?_, ?_⟩
    · have e : algebraMap F E ((g.q * s : 𝒪[F]) : F) * y =
          algebraMap F E (g.q : F) * (algebraMap F E (s : F) * y) := by
        rw [MulMemClass.coe_mul, map_mul, mul_assoc]
      rw [e, map_mul, AlgEquiv.commutes]
      ext <;> simp
    · have hq : ∀ t : 𝒪[F], Ideal.Quotient.mk (Ideal.span {g.q}) (g.q * t) = 0 := fun t =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right t _ (Ideal.mem_span_singleton_self _))
      rw [hq, hq]

theorem common_denom (M : Loc.Model F E) {ι : Type} [Fintype ι] (y : ι → E) :
    ∃ a : 𝒪[F], a ≠ 0 ∧ ∀ k, algebraMap F E (a : F) * y k ∈ M.R := by
  classical
  choose d hd0 hd using fun k => R_denom M (y k)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k, fun k => ?_⟩
  have hp : (∏ j, d j) = (∏ j ∈ Finset.univ.erase k, d j) * d k :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ k)).symm
  rw [hp]
  have e : algebraMap F E (((∏ j ∈ Finset.univ.erase k, d j) * d k : 𝒪[F]) : F) * y k =
      algebraMap F E ((∏ j ∈ Finset.univ.erase k, d j : 𝒪[F]) : F) * (algebraMap F E (d k : F) * y k) := by
    rw [MulMemClass.coe_mul, map_mul, mul_assoc]
  rw [e]
  exact M.R.mul_mem (alg_mem_R M _) (hd k)

end LocTop

end Formalism.L2.SG.Pf.ProdEP2Uni
end
end
