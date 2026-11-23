module

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GramMMUnitOfTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle007
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.Bundle030
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.IsLoUniConjTranspose
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle020

@[expose] public section

section

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Uni

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  apply Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_mul <;> assumption

theorem loUni_iff_ct {A : Matrix (Fin N) (Fin N) K} [StarRing K] : IsLoUni A ↔ IsUpUni Aᴴ := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · rw [conjTranspose_apply, (h j i).1 hji, star_zero]
    · subst hij; rw [conjTranspose_apply, (h i i).2 rfl, star_one]
  · intro h i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have := (h j i).1 hij
      rw [conjTranspose_apply] at this
      exact star_eq_zero.1 this
    · subst hij
      have := (h i i).2 rfl
      rw [conjTranspose_apply] at this
      rw [← star_star (A i i), this, star_one]

theorem upUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem loUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem upUni_inv {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : IsUpUni A⁻¹ := by
  apply Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_inv <;> assumption

theorem loUni_mul {A B : Matrix (Fin N) (Fin N) K} [StarRing K] (hA : IsLoUni A) (hB : IsLoUni B) :
    IsLoUni (A * B) := by
  rw [loUni_iff_ct, conjTranspose_mul]
  exact upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)

theorem loUni_inv {A : Matrix (Fin N) (Fin N) K} [StarRing K] (h : IsLoUni A) : IsLoUni A⁻¹ := by
  rw [loUni_iff_ct, conjTranspose_nonsing_inv]
  exact upUni_inv (loUni_iff_ct.1 h)

theorem upUni_last {r : ℕ} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni A) (c : Fin (r + 1)) :
    A (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  by_cases hc : c = Fin.last r
  · subst hc; rw [if_pos rfl]; exact (h _ _).2 rfl
  · rw [if_neg hc]
    exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)

end Uni

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem flag_of_upUni (F : FlagG S r T) (g : S.V →ₗ[E] S.V) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : IsUpUni N) (hg : ∀ b, g (F.fvec b) = ∑ c, N c b • F.fvec c) :
    (∀ j, ∀ x ∈ F.Xa (j + 1), g x - x ∈ F.Xa j) ∧ g F.z - F.z ∈ F.X := by
  have hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c := by
    intro b
    rw [hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]
    have h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b := by
      rw [Finset.sum_eq_single b]
      · rw [(hN b b).2 rfl, one_smul]
      · intro c hc hcb
        have : b < c := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)
        rw [(hN c b).1 this, zero_smul]
      · intro hb; exfalso; apply hb; simp
    rw [h2]; abel
  have he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a := by
    intro a
    have := hdiff (Fin.castSucc a)
    simp only [FlagG.fvec, Fin.snoc_castSucc] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc' : c < Fin.castSucc a := (Finset.mem_filter.1 hc).2
    have hcl : c ≠ Fin.last r := ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', by simpa using hc', rfl⟩
  refine ⟨fun j x hx => ?_, ?_⟩
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have ha' : (a : ℕ) < j + 1 := ha
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_sub_add_comm]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · have := hdiff (Fin.last r)
    simp only [FlagG.fvec, Fin.snoc_last] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hcl : c ≠ Fin.last r := ne_of_lt (Finset.mem_filter.1 hc).2
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', rfl⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem comp_mem {x : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O) :
    (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp] ∧ (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(Z.M p).L.O_def] at hx
  have h := hx.map (g.e.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  have h1 := h.map ((AlgHom.fst (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  have h2 := h.map ((AlgHom.snd (D.s.atP p).Fp (D.s.atP p).Fp (D.s.atP p).Fp).restrictScalars 𝒪[(D.s.atP p).Fp])
  exact ⟨PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h1, PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral h2⟩

theorem mem_R_of (hs : (Z.M p).split = some g) {x : (D.s.atP p).Ep}
    (h1 : (g.e x).1 ∈ 𝒪[(D.s.atP p).Fp]) (h2 : (g.e x).2 ∈ 𝒪[(D.s.atP p).Fp])
    (h3 : ∃ o ∈ 𝒪[(D.s.atP p).Fp], (g.e x).1 - (g.e x).2 = (g.q : (D.s.atP p).Fp) * o) : x ∈ (Z.M p).R := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, ?_⟩
  · simp only [RingHom.mem_eqLocus, RingHom.comp_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    obtain ⟨o, ho, he⟩ := h3
    refine ⟨⟨o, ho⟩, ?_⟩
    apply Subtype.ext
    show o * (g.q : (D.s.atP p).Fp) = (g.e x).1 - (g.e x).2
    rw [he, mul_comm]
  · rfl

def emap (Y : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (Y a b)).1 / (g.q : (D.s.atP p).Fp), -((g.e (Y b a)).2 / (g.q : (D.s.atP p).Fp)))

def lmat (l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => g.e.symm ((g.e (l a b)).1, (g.e (ρ b a)).2)

theorem emap_mul (l Y ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) :
    emap Z p g (l * Y * ρ) = lmat Z p g l ρ * emap Z p g Y * lmat Z p g ρ l := by
  ext a b
  apply g.e.injective

  simp only [emap, lmat, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  ext
  · simp only [Prod.fst_sum, Prod.fst_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  · simp only [Prod.snd_sum, Prod.snd_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div, neg_div,
      ← Finset.sum_neg_distrib, mul_neg, neg_mul]
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    ring

end Split

end Formalism.L2.SG.Pf.FibQ
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def VolOneAEC : Prop :=
  {v : PlX X | ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧ (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)}.Finite

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG4

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_fwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hI : Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩) :
    (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) ⊆
      GamR H t₂ (algebraMap F E (g.q : F)) := by
  set c : E := algebraMap F E (g.q : F) with hc
  have hcO : c ∈ M.L.O := q_mem_O g
  have hcL : ∀ (Λ : Submodule M.L.O V) {x : V}, x ∈ Λ → c • x ∈ Λ := by
    intro Λ x hx
    exact Λ.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  have hMMU : ∀ (t : Term V M r) {x : V}, x ∈ MMsharp H t →
      x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
    intro t x hx
    have h1 : x ∈ Submodule.span E (Set.range (H.MMfam t)) := hx.1
    refine Submodule.span_le.mpr ?_ h1
    rintro _ ⟨i, rfl⟩
    have hle : H.Xp t.f ⊔ H.Xp t.f' ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) :=
      sup_le
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inl j, rfl⟩))
        (Submodule.span_mono (by
          rintro _ ⟨j, rfl⟩
          exact ⟨Sum.inr j, rfl⟩))
    exact hle (MMfam_mem_sup H t i)
  rintro _ ⟨p, ⟨u, u', u'', hu, hu', hd, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := D.hsurj₁ u
  obtain ⟨w'', hw''⟩ := D.hsurj₁ u''
  obtain ⟨w', hw'c⟩ : ∃ w' : ↥(H.W0 t₁.f t₁.f'), (w' : V) = (w : V) - c • (w'' : V) :=
    ⟨w - c • w'', rfl⟩
  have hw'eq : w' = w - c • w'' := Subtype.ext (by rw [hw'c]; rfl)
  have hψw' : (ψ w' : V) = (ψ w : V) - c • (ψ w'' : V) := by
    rw [hw'eq, map_sub, map_smul]
    rfl
  have hx : (u : V) + w ∈ H.perp (H.X t₁.f) := Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H w.2)
  have hx' : (u' : V) + w' ∈ H.perp (H.X t₁.f') := Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H w'.2)
  have hxL' : (u' : V) + w' ∈ t₁.abelian₂ := by
    have e : (u' : V) + w' = ((u : V) + w) - c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.sub_mem _ hw (hcL _ hw'')
  have hdiffL : ((u : V) + w) - ((u' : V) + w') ∈ H.smulLat c t₁.abelian₂ := by
    have e : ((u : V) + w) - ((u' : V) + w') = c • ((u'' : V) + w'') := by
      rw [hw'c, smul_add, ← hd]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hw'', rfl⟩
  have hmem : (φ' (H.mkW t₁.f' ⟨_, hx'⟩), φ (H.mkW t₁.f ⟨_, hx⟩)) ∈
      H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
    rw [← hI]
    exact ⟨_, ⟨⟨_, hx'⟩, ⟨_, hx⟩, hxL', hw, hdiffL, rfl⟩, rfl⟩
  obtain ⟨y', y, hy'L, hyL, hyd, hyeq⟩ := hmem
  rw [Prod.mk.injEq] at hyeq
  obtain ⟨hyeq', hyeq2⟩ := hyeq
  obtain ⟨z, hzL, hz⟩ := exists_of_mem_smulLat H hyd
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (y : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (y' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ z
  have hx₂ : a + b ∈ H.perp (H.X t₂.f) := by
    rw [hab]
    exact y.2
  have hx₂' : a' + b' ∈ H.perp (H.X t₂.f') := by
    rw [hab']
    exact y'.2
  have hap : a ∈ H.perp (H.X t₂.f) := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp H hb) hx₂
  have hap' : a' ∈ H.perp (H.X t₂.f') := perp_left H (mem_perp_isotropicSpan_of_mem_framePerp' H hb') hx₂'
  have h1 : φ (H.mkW t₁.f ⟨_, hx⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩ :=
    hyeq2.trans (congrArg _ (Subtype.ext hab.symm))
  have h1' : φ' (H.mkW t₁.f' ⟨_, hx'⟩) = H.mkW t₂.f' ⟨a' + b', hx₂'⟩ :=
    hyeq'.trans (congrArg _ (Subtype.ext hab'.symm))
  obtain ⟨hbψ, hφ⟩ := RGHyp.trF H D (hMMU t₁ u.2) hu w hx ha hb hap hx₂ h1
  obtain ⟨hb'ψ, hφ'⟩ := RGHyp.trF' H D (hMMU t₁ u'.2) hu' w' hx' ha' hb' hap' hx₂' h1'
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hz
  have hb''ψ : b'' = ψ w'' := by
    apply smul_cancel_q g
    rw [← hdb, hbψ, hb'ψ, hψw']
    abel
  have haM : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb (by rw [hab]; exact hyL)
  have ha'M : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' (by rw [hab']; exact hy'L)
  have ha''M : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' (by rw [hab'']; exact hzL)
  refine ⟨⟨a, haM⟩, ⟨a', ha'M⟩, ⟨a'', ha''M⟩, hap, hap', hda, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext hφ hφ'))
  · exact (D.hθ u ⟨a, haM⟩).mpr ⟨w, hw, by rw [← hbψ, hab]; exact hyL⟩
  · exact (D.hθ u'' ⟨a'', ha''M⟩).mpr ⟨w'', hw'', by rw [← hb''ψ, hab'']; exact hzL⟩

end RG4

end Formalism.L2.SG.LsDatumA
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG7

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

private theorem add_psi_symm_mem_lam_of_theta_ddMk_eq {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (m₁ : MMsharp H t₁) (m₂ : MMsharp H t₂) (h : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂)
    (b : H.W0 t₂.f t₂.f') (hb : (m₂ : V) + (b : V) ∈ Λ₂) :
    (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := (D.hθ m₁ m₂).1 h
  have key : ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [D.hth]
    have e : ((ψ (ψ.symm b - w) : H.W0 t₂.f t₂.f') : V) = ((m₂ : V) + (b : V)) - ((m₂ : V) + ((ψ w : H.W0 t₂.f t₂.f') : V)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, Submodule.coe_sub]
      abel
    rw [e]
    exact Λ₂.sub_mem hb hw₂
  have e2 : (m₁ : V) + ((ψ.symm b : H.W0 t₁.f t₁.f') : V) = ((m₁ : V) + (w : V)) + ((ψ.symm b - w : H.W0 t₁.f t₁.f') : V) := by
    rw [Submodule.coe_sub]
    abel
  rw [e2]
  exact t₁.abelian₂.add_mem hw₁ key

theorem rg_bwd_sup (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ ⊆ Prod.map φ' φ '' H.iotaGraph g t₁ := by
  rintro p ⟨x', x, hx'L, hxL, hdiff, rfl⟩
  obtain ⟨l, hl, hl_eq⟩ := exists_of_mem_smulLat H hdiff
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₂ (x : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₂ (x' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₂ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₂ _ ha ha' ha'' hb hb' hb'' hab hab' hab'' hl_eq
  have hxL2 : a + b ∈ Λ₂ := by rw [hab]; exact hxL
  have hx'L2 : a' + b' ∈ Λ₂ := by rw [hab']; exact hx'L
  have hlL2 : a'' + b'' ∈ Λ₂ := by rw [hab'']; exact hl
  have sa : a ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha hb hxL2
  have sa' : a' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha' hb' hx'L2
  have sa'' : a'' ∈ MMsharp H t₂ := part_MMsharp H t₂ Λ₂ D.hsd₂ D.hMM₂ ha'' hb'' hlL2
  have pa : a ∈ H.perp (H.X t₂.f) := by
    have e : a = (x : V) - b := by rw [← hab]; abel
    rw [e]
    exact Submodule.sub_mem _ x.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have pa' : a' ∈ H.perp (H.X t₂.f') := by
    have e : a' = (x' : V) - b' := by rw [← hab']; abel
    rw [e]
    exact Submodule.sub_mem _ x'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have hmem : (ddMk H t₂ ⟨a, sa⟩, ddMk H t₂ ⟨a'', sa''⟩, H.mkW t₂.f ⟨a, pa⟩, H.mkW t₂.f' ⟨a', pa'⟩) ∈
      GamR H t₂ (algebraMap F E (g.q : F)) :=
    ⟨⟨a, sa⟩, ⟨a', sa'⟩, ⟨a'', sa''⟩, pa, pa', hda, rfl⟩
  rw [← hG] at hmem
  obtain ⟨q, ⟨u, u', u'', hu, hu', hdu, rfl⟩, hq⟩ := hmem
  simp only [Prod.mk.injEq] at hq
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hy := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u ⟨a, sa⟩ h1 ⟨b, hb⟩ hxL2
  have hy'' := add_psi_symm_mem_lam_of_theta_ddMk_eq H D u'' ⟨a'', sa''⟩ h2 ⟨b'', hb''⟩ hlL2
  have hn' : ψ.symm ⟨b', hb'⟩ = ψ.symm ⟨b, hb⟩ - (algebraMap F E (g.q : F)) • ψ.symm ⟨b'', hb''⟩ := by
    rw [← map_smul, ← map_sub]
    congr 1
    ext
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rw [← hdb]
    abel
  have hu'e : (u' : V) = (u : V) - (algebraMap F E (g.q : F)) • (u'' : V) := by
    rw [← hdu]; abel
  have hy'e : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) =
      ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
        (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) := by
    rw [hn', hu'e, Submodule.coe_sub, Submodule.coe_smul, smul_add]
    abel
  have py : (u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f) :=
    Submodule.add_mem _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2)
  have py' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ H.perp (H.X t₁.f') :=
    Submodule.add_mem _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2)
  have hcy : (algebraMap F E (g.q : F)) • ((u'' : V) + ((ψ.symm ⟨b'', hb''⟩ : H.W0 t₁.f t₁.f') : V)) ∈ t₁.abelian₂ :=
    smul_mem_lat g t₁.abelian₂ hy''
  have hyL' : (u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
    rw [hy'e]; exact t₁.abelian₂.sub_mem hy hcy
  have hdL : ((u : V) + ((ψ.symm ⟨b, hb⟩ : H.W0 t₁.f t₁.f') : V)) -
      ((u' : V) + ((ψ.symm ⟨b', hb'⟩ : H.W0 t₁.f t₁.f') : V)) ∈
      H.smulLat (algebraMap F E (g.q : F)) t₁.abelian₂ := by
    rw [hy'e, sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hy'', rfl⟩
  refine ⟨(H.mkW t₁.f' ⟨_, py'⟩, H.mkW t₁.f ⟨_, py⟩), ⟨⟨_, py'⟩, ⟨_, py⟩, hyL', hy, hdL, rfl⟩, ?_⟩
  simp only [Prod.map]
  congr 1
  · rw [mkW_add H _ _ hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ.symm ⟨b', hb'⟩).2), map_add (f := _), h4, D.hC1',
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab'
  · rw [mkW_add H _ _ hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ.symm ⟨b, hb⟩).2), map_add (f := _), h3, D.hC1,
      LinearEquiv.apply_symm_apply, ← mkW_add]
    exact mkW_congr H _ _ hab

end RG7

end Formalism.L2.SG.LsDatumA
end
end
