module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle003
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle022
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.DualFormInverse

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_one {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p : ι} {α : K}
    (hα : α ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p := by
  refine ⟨fun t => if t = p then α else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    · exact hα
    · exact S.zero_mem
  · rw [Fintype.sum_eq_single p]
    · simp
    · intro t ht
      simp [ht]

theorem exists_two {ι : Type} [Fintype ι] [DecidableEq ι] {S : Subring K} {p q : ι} (hpq : p ≠ q)
    {α β : K} (hα : α ∈ S) (hβ : β ∈ S) (g : ι → ι → K) :
    ∃ κ : ι → K, (∀ t, κ t ∈ S) ∧ ∀ s, ∑ t, κ t * g s t = α * g s p + β * g s q := by
  refine ⟨fun t => if t = p then α else if t = q then β else 0, fun t => ?_, fun s => ?_⟩
  · dsimp only
    split_ifs
    exacts [hα, hβ, S.zero_mem]
  · rw [Fintype.sum_eq_add p q hpq]
    · simp [hpq.symm]
    · rintro t ⟨h1, h2⟩
      simp [h1, h2]

theorem dualF_le_of_inv {ι : Type} [Fintype ι] [DecidableEq ι] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hnd : Nondeg h) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (G : ι → V)
    (hG : Submodule.span K (Set.range G) = ⊤)
    (hinv : ∀ u, ∃ κ : ι → K, (∀ t, κ t ∈ SP K 𝔭) ∧
      ∀ s, ∑ t, κ t * h (G s) (G t) = if s = u then 1 else 0) :
    dualF h 𝔭 (locF 𝔭 (Submodule.span (𝓞 K) (Set.range G))) ≤
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range G)) := by
  choose κ hκS hκ using hinv
  intro x hx
  have hX : ∀ u, h (G u) x ∈ SP K 𝔭 := fun u => by
    rw [mem_SP_iff_locF]
    exact hx (G u) (LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨u, rfl⟩))
  have hyx : ∀ s, h (G s) (x - ∑ t, (∑ u, κ u t * h (G u) x) • G t) = 0 := by
    intro s

    rw [map_sub, map_sum]
    simp only [form_smul_right]
    have e : ∀ t, (∑ u, κ u t * h (G u) x) * h (G s) (G t) =
        ∑ u, h (G u) x * (κ u t * h (G s) (G t)) := fun t => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
    simp only [← Finset.mul_sum, hκ]
    simp
  have hxy := eq_zero_of_orth hs hnd G hG hyx
  rw [sub_eq_zero] at hxy
  rw [hxy]
  refine Submodule.sum_mem _ fun t _ => smul_mem_locF_of_SP ?_ (Submodule.subset_span ⟨t, rfl⟩)
  exact (SP K 𝔭).sum_mem fun u _ => (SP K 𝔭).mul_mem (hκS u t) (hX u)

end Formalism.L2.SG.Pf.DualFormInverse
end
end

section

noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable (D : Formalism.BasicNotions.D7)

theorem emb_G {T T' : ℕ} (Z : MatZ D) (φ : D.host.E →+* ℂ) :
    φ (GZ (T : D.host.E) (T' : D.host.E) Z) =
      ((Complex.normSq (φ Z.det) - (T : ℝ) * T' * Complex.normSq (φ (leadMinorE Z D.R.rS)) : ℝ) : ℂ) := by
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have hfull : leadMinorE Z (D.R.rS + 1) = Z.det := by
    unfold leadMinorE
    rw [dite_eq_left le_rfl]
    rfl
  rw [GZ, hfull]
  simp only [map_sub, map_mul, map_natCast, hφ, Complex.mul_conj]
  push_cast
  ring

theorem det_ne_of_totPos {T T' : ℕ} (Z : MatZ D) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (T : D.host.E) (T' : D.host.E) Z)) :
    Z.det ≠ 0 := by
  intro h0
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; have h := D.R.m_le_f; have h₂ := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    omega)
  obtain ⟨τ⟩ := this
  have h1 := hP τ
  rw [emb_G D Z, Complex.ofReal_re, h0, map_zero, Complex.normSq_zero, zero_sub] at h1
  have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Nat.cast_nonneg (α := ℝ) T'))
    (Complex.normSq_nonneg (D.host.emb (D.eTau τ) (leadMinorE Z D.R.rS)))
  linarith

theorem inv_last (Z : MatZ D) (hdet : Z.det ≠ 0) :
    Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) = leadMinorE Z D.R.rS / Z.det := by
  have hprev : leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
    unfold leadMinorE
    rw [dite_eq_left (Nat.le_succ _)]
    rfl
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
    PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_updateRow_last_single, ← hprev,
    Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

theorem gam'_last (N' : ℕ) (Z : MatZ D) :
    Gam' N' Z (Fin.last D.R.rS) (Fin.last D.R.rS) =
      -(N' : D.host.E) * (star (Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) * Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) := by
  simp only [Gam', Gam, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, ite_and]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_ite, ite_mul]
  ring

theorem tv_star (N N' : ℕ) (Z : MatZ D) : star (tv N N' Z) = tv N N' Z := by
  rw [tv, star_add, gam'_herm, star_inv₀, star_natCast]

theorem tv_pos (hD : TotPosAll) {N N' : ℕ} (hN : 0 < N) (Z : MatZ D)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (N : D.host.E) (N' : D.host.E) Z)) :
    Formalism.HermitianLattices.Ext.L3.TotPos (tv N N' Z) := by
  have hdet := det_ne_of_totPos D Z hP
  have hGs : star (GZ (N : D.host.E) (N' : D.host.E) Z) = GZ (N : D.host.E) (N' : D.host.E) Z := by
    simp only [GZ, star_sub, star_mul, star_star, star_natCast]
    ring
  have hG := hD D _ hGs hP
  intro φ
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have h1 := hG φ
  rw [emb_G D Z, Complex.ofReal_re] at h1
  have hA : 0 < Complex.normSq (φ Z.det) := Complex.normSq_pos.2 ((map_ne_zero φ).2 hdet)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : φ (tv N N' Z) = (((N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) /
      Complex.normSq (φ Z.det)) : ℝ) : ℂ) := by
    rw [tv, gam'_last, inv_last D Z hdet]
    simp only [map_add (f := _), map_mul, map_neg, map_natCast, map_inv₀, hφ, map_div₀, star_div₀]
    rw [div_mul_div_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [ht, Complex.ofReal_re]
  have e : (N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) / Complex.normSq (φ Z.det)) =
      (Complex.normSq (φ Z.det) - N * N' * Complex.normSq (φ (leadMinorE Z D.R.rS))) /
        (N * Complex.normSq (φ Z.det)) := by
    field_simp
  rw [e]
  exact div_pos h1 (mul_pos hNr hA)

end D7

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ratPair_of (hD : TotPosAll) : RatPair := by
  intro D u u' _ F0 what₂ _ Z hP
  have hN : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  obtain ⟨y, hy⟩ := dual_of_flag D hN F0
  have hdet := det_ne_of_totPos D Z hP
  obtain ⟨w0, hw0, hwt⟩ := exists_W_vec D hN hy (tv (D.mem u).A.T (D.mem u').A.T Z)
    (tv_star D _ _ Z) (tv_pos D hD hN Z hP)
  set p := pv F0.e y F0.z (D.mem u).A.T (D.mem u').A.T Z w0 with hp
  set f' : Fin (D.R.rS + 1) → (VS D).V := fun b => ∑ a, Z a b • p a with hf'
  have hfp : ∀ a a', (VS D).hT (F0.fvec a) (p a') = if a = a' then 1 else 0 :=
    fun a a' => hf_pv hy hN hw0 a a'
  have hpp : ∀ a a', (VS D).hT (p a) (p a') = Gam' (D.mem u').A.T Z a a' := hpv_pv hy hN hw0 hwt
  have hzh : ∀ a b, (VS D).hT (F0.fvec a) (f' b) = Z a b := by
    intro a b

    simp only [hf', map_sum, map_smul, smul_eq_mul, hfp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hgr : ∀ b c, (VS D).hT (f' b) (f' c) = Gam D.host.E D.R.rS (D.mem u').A.T b c := by
    intro b c
    rw [hf', gram_comb' p Z b c]
    have h1 : Matrix.of (fun a a' => (VS D).hT (p a) (p a')) = Gam' (D.mem u').A.T Z := by
      ext a a'; simp [hpp]
    have hinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.2 hdet)
    rw [h1, Gam']
    simp only [Matrix.mul_assoc]
    rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hne : ∀ d : Fin D.R.rS, Fin.castSucc d ≠ Fin.last D.R.rS := fun d => (Fin.castSucc_lt_last d).ne
  have hind : LinearIndependent D.host.E (fun d : Fin D.R.rS => f' (Fin.castSucc d)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc d
    have hv : Z.mulVec (Fin.snoc (α := fun _ => D.host.E) c 0) = 0 := by
      funext a
      have h1 := congrArg ((VS D).hT (F0.fvec a)) hc

      rw [map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hzh] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
    simpa using congrFun this (Fin.castSucc d)
  let Fl : FlagG (VS D) D.R.rS (Tn u') :=
    { e := fun d => f' (Fin.castSucc d)
      z := f' (Fin.last D.R.rS)
      e_indep := hind
      e_iso := fun a b => by rw [hgr]; simp [Gam, hne]
      z_orth := fun a => by rw [hgr]; simp [Gam, hne]
      z_norm := by rw [hgr]; simp [Gam, Tn] }
  refine ⟨⟨Fl, f' (Fin.last D.R.rS)⟩, rfl, ?_⟩
  funext a b
  have hfv : Fl.fvec b = f' b := by
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, Fl]
    | cast b => simp [FlagG.fvec, Fl]
  show brS (VS D) (Fl.fvec b) (F0.fvec a) = Z a b
  rw [brS, hfv, hzh]

end Formalism.L2.SG.Pf.Cnt
end
end

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem algebraMap_mem_LO (c : F) (hc : c ∈ 𝒪[F]) : algebraMap F E c ∈ M.L.O := by
  rw [M.L.O_def]
  have h := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨c, hc⟩)
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h
  exact h

theorem dens_eq_zero_of_not_mem (H : Loc.HermSp M V) (ϖ : 𝒪[F]) {abelian₂ : Submodule M.L.O V} (hSD : H.IsSelfDual abelian₂)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (a b : ι) (hab : G₀ a b ∉ M.L.O) : H.dens ϖ abelian₂ G₀ = 0 := by
  unfold Loc.HermSp.dens
  have hE : IsEmpty {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} := by
    refine ⟨fun v => hab ?_⟩
    obtain ⟨hP, hG⟩ := v.2
    have h1 : H.h (v.1 b) (v.1 a) ∈ M.L.O := (hSD.2.2 (v.1 b)).1 (hP.1 b) (v.1 a) (hP.1 a)
    have h2 := hG a b
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
    have hϖ : algebraMap F E (ϖ : F) ∈ M.L.O := algebraMap_mem_LO _ ϖ.2
    have h3 : H.h (v.1 b) (v.1 a) - G₀ a b ∈ M.L.O := by
      rw [← hc]
      exact M.L.O.mul_mem c.2 hϖ
    have h4 : G₀ a b = H.h (v.1 b) (v.1 a) - (H.h (v.1 b) (v.1 a) - G₀ a b) := by ring
    rw [h4]
    exact M.L.O.sub_mem h1 h3
  have h0 : Set.range (fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - G₀ a b ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
        fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) = ∅ :=
    Set.range_eq_empty _
  rw [h0]
  simp

end Local

def GaPlusIntMM : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (∀ (p : PlF D) (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)),
          GaPlus M δ p (Tn u) (Tn u') Z a b ∈ (M p).L.O) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F')

theorem notIntDens_of (h1 : LocSelfDual) (hG : GaPlusIntMM) : NotIntDens := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI
  by_contra hall
  push_neg at hall
  apply hI
  refine hG D δ M hA L u u' hT F0 what₂ hR Z F' hz hZ hP fun p a b => ?_
  by_contra hab
  exact hall p (dens_eq_zero_of_not_mem (L.H p) (ϖ p) (h1 D δ M hA L p) _ a b hab)

end Formalism.L2.SG.Pf.Cnt
end
end
