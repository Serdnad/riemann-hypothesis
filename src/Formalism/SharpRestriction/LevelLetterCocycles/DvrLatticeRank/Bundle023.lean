module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle018
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle020
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle019
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHyp
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfA
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
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle006

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLJ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem local_form (hwd : MLF.WD W T Pt π' c) {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ)
    (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h') (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    (u : LL) (hu : u ≠ 0) (hu1 : ∀ i : ℤ, i ≠ 0 → u ^ i ≠ 1)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    (hsimp : ∀ τ ζ, Pt c ζ τ → ∃ U : PowerSeries LL, W.lev c ζ (Eπ ^ h') = PowerSeries.X ^ h' * U ∧
      PowerSeries.constantCoeff U ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hγ : γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c) :
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i) := by
  intro τ ζ hpt f hf i hi
  obtain ⟨⟨m₀, hf0⟩, m, a, y, hr, hfe⟩ := hf
  have hfb : MLG.Bdd f m₀ := hf0

  have hrγ := MLH.rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr
  have hrn := MLE.rep_smul W T π' Eπ h' c hr (W.AΔ.algebraMap_mem (-1 : O))
  rw [← MLE.smul_eq_smulLA, neg_one_smul] at hrn
  have hra := MLE.rep_append W T π' Eπ h' c hrγ hrn
  rw [← sub_eq_add_neg] at hra
  have hgood := MLF.good_all W T Pt π' Eπ h' c hwd hγ hra τ ζ hpt
  rw [MLE.expS_append] at hgood
  set e := expS W T c ζ (fun j => (a j : LetA O n)) y with he
  have heb : MLG.Bdd e 0 := fun j hj => MLI.expS_neg W T c ζ _ y hj

  have hneg : expS W T c ζ (fun j => ((⟨algebraMap O (LetA O n) (-1) * a j,
      W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (a j).2⟩ : ↥W.AΔ) : LetA O n)) y = -e := by
    show expS W T c ζ (fun j => algebraMap O (LetA O n) (-1) * (a j : LetA O n)) y = -e
    rw [MLF.expS_alg_mul, map_neg, map_one, neg_one_smul]
  obtain ⟨U, hU, hU0⟩ := hsimp τ ζ hpt
  have hfu : MLG.Bdd (fun s => u ^ s • f s) m₀ := fun s hs => by simp only [hfb s hs, smul_zero]
  have hγpart : ∀ j, expS W T c ζ (fun k => ((⟨u₀ * W.γA W.gamK (a k), W.AΔ.mul_mem hu₀
      (MLH.γA_mem_AΔ W (a k).2)⟩ : ↥W.AΔ) : LetA O n)) y j =
      serMul (W.lev c ζ (Eπ ^ h')) (fun s => u ^ s • f s) j := by
    intro j
    show expS W T c ζ (fun k => u₀ * W.γA W.gamK (a k)) y j = _
    have hLdec : W.lev c ζ (Eπ ^ h') = W.lev c ζ u₀ * PowerSeries.rescale u (W.lev c ζ (Eπ ^ h')) := by
      rw [← hlev τ ζ hpt, ← map_mul, hΛ]
    rw [MLB.expS_mul, hLdec, ← MLG.serMul_serMul _ _ hfu]
    have hin : serMul (PowerSeries.rescale u (W.lev c ζ (Eπ ^ h'))) (fun s => u ^ s • f s) =
        fun s => u ^ s • e s := by
      funext s
      rw [← MLG.serMul_rescale u hu, hfe s]
    rw [hin, MLG.serMul_eq_sum (m₀ := 0) _ (fun s hs => by simp only [heb s hs, smul_zero]) j (j.toNat + 1) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MLH.expS_γ W T c ζ u (hlev τ ζ hpt)]
    congr 1
    by_cases hjk : 0 ≤ j - (k : ℤ)
    · rw [← zpow_natCast, Int.toNat_of_nonneg hjk]
    · rw [MLI.expS_neg W T c ζ _ y (by omega), heb _ (by omega), smul_zero, smul_zero]

  set g : ℤ → T.V ⊗[Qp] BdR := fun s => u ^ s • f s - f s with hgdef
  have hgb : MLG.Bdd g m₀ := fun s hs => by simp [hgdef, hfb s hs]
  have hGg : ∀ j, serMul (W.lev c ζ (Eπ ^ h')) g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - j) := by
    intro j
    have h1 := hgood j
    rw [Pi.add_apply, hγpart j, hneg, Pi.neg_apply, ← hfe j, ← sub_eq_add_neg] at h1
    convert h1 using 1
    rw [MLG.serMul_eq_sum _ hgb j _ le_rfl, MLG.serMul_eq_sum _ hfu j _ le_rfl,
      MLG.serMul_eq_sum _ hfb j _ le_rfl, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef, smul_sub]
  have hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro j
    have h1 := hGg (j + h')
    rw [hU, ← MLG.serMul_serMul _ _ hgb, MLG.serMul_X_pow, add_sub_cancel_right] at h1
    convert h1 using 2
    ring
  have hgi := MLI.ind_fil T τ U hU0 hgb hH i
  have e1 : g i = (u ^ i - 1) • f i := by rw [hgdef, sub_smul, one_smul]
  rw [e1] at hgi
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.2 (hu1 i hi))).1 hgi

end Generic

end Formalism.MainNotions.N.Ln34.MLJ

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct Formalism.MainNotions.N.Ln34.ModelFPf

theorem rec_WD (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    MLF.WD ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c := by
  intro τ ζ hpt m m' a y hy b z hz h
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hprim : IsPrimitiveRoot ζ l := framepf_pt_prim D HW hG c ζ τ hpt
  have hprim' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hp]; exact hprim
  haveI : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨-, -, -, h4W, -⟩ := hA.1 l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 letπ) = 0 := by
    rw [CrystallineExponents.cc_lev_pi ((HW l).W K 1 LL hG) (c - 1) 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hπ : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 π') = 0 := by
    obtain ⟨w, hw⟩ := hr.2.2.1
    rw [hw, map_mul, map_pow, map_mul, map_pow, hπ1, zero_pow (by omega), mul_zero]
  have hQ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hprim'
  have hP : MLA.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
    refine ⟨hT, ⟨1, by rw [pow_one]; exact hprim'⟩, hprim'.pow_eq_one, hQ.1, hQ.2, ?_, ?_⟩
    · intro x k hk
      have h4 := ((h4W T hT).1 (c - 1) 1 ⟨0, by simp⟩ (by rw [hX]; exact hπ1)).1 x k
      exact h4.2 hk
    · intro x hx
      exact ((HW l).W K 1 LL hG).N_φ T x hx
  exact MLA.expS_wd ((Cm l).C K 1 LL hG).tie T hinj hP π' hπ a y hy b z hz h


theorem exists_mul_gamma_Eat_pow_eq_Eat_pow (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) :
    ∃ u₀ ∈ ((HW l).W K 1 LL hG).AΔ, u₀ * ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK
      (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hr
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  refine ⟨((hu.unit⁻¹ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ) : LetA _ _) ^ h', Subalgebra.pow_mem _ hu'Δ h', ?_⟩
  rw [hgam, map_pow, hγ, mul_pow, ← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]


theorem rec_lev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) :
    ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK a) =
      PowerSeries.rescale (algebraMap ↥(OL LL) ↥LL.1
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hprim : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by
    rw [pow_one, hp]; exact framepf_pt_prim D HW hG c ζ τ hpt
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
    rw [hgam, Nat.cast_one (R := ↥LL.1), ((HW l).W K 1 LL hG).gam_gen, hs]
  have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 hprim hv (by rw [pow_one]) a
  exact this


theorem rec_u (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) :
    algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) :
      ↥(OL LL)) ≠ 0 ∧
    ∀ i : ℤ, i ≠ 0 → (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ
      ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL))) ^ i ≠ 1 := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have har := (framepf_hyp_arith D HW l hl K LL hG 1 hsK).1
  rw [hgam]
  set χ := ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) with hχ
  have hnat : ∀ k : ℕ, 1 ≤ k → (algebraMap ↥(OL LL) ↥LL.1 χ) ^ k ≠ 1 := by
    intro k hk h1
    have h2 : χ ^ k = 1 := by
      apply Subtype.val_injective
      have := h1
      rw [← map_pow] at this
      simpa using this
    apply har k hk
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  refine ⟨((Units.isUnit _).map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero, fun i hi h1 => ?_⟩
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · apply hnat (-i).toNat (by omega)
    have : (algebraMap ↥(OL LL) ↥LL.1 χ) ^ (-i) = 1 := by rw [zpow_neg, h1, inv_one]
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · apply hnat i.toNat (by omega)
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]

end Formalism.MainNotions.N.Ln34.MLL

end
end
