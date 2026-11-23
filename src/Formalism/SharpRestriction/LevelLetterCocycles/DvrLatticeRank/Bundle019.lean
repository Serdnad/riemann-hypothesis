module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle011
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.ModelFPf

theorem modelflink_pf : ModelFLinkStep := by
  intro D HW F Cm CA CB CK hA hP l _ hl K LL hG π' E hπ h' hh' c α β hfr T hcry hjmp
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, -, -, h4W, h5W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨h5a, h5b, -⟩ := h5W T (fun _ => h') (fun _ => h') hcry (fun τ _ _ => hjmp τ)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hπ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hQ : ((HW l).W K 1 LL hG).Q = (w : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
    rw [Q_eq_q _ hs]
    exact hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hM : 1 ≤ MK l K h' := by
    refine Nat.one_le_ceil_iff.2 (div_pos ?_ ?_)
    · have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    · exact_mod_cast hsK
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hpt : ∀ ζ τ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 := by
    intro ζ τ hPt
    obtain ⟨τs, hIs, -⟩ := hPt
    have hz1 : (D.loc l).ζQ 1 ^ l = 1 := by
      rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
    have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 :=
      le_sup_right (a := K0 K) (IntermediateField.subset_adjoin _ _ (by rw [pow_one]; exact hz1))
    have hy := hIs.2 ⟨_, hmem⟩ rfl
    have hyl : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz1)
    refine ⟨?_, ?_⟩
    · rw [hp, ← hy, ← map_pow, hyl, map_one]
    · intro h1
      rw [← hy] at h1
      have : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 := τs.toRingHom.injective (by rw [map_one]; exact h1)
      exact (D.loc l).ζQ_one (congrArg Subtype.val this)
  exact modelF_local ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (MK l K h') (sigA l (sK l K) h') c α β hfr hcry hjmp hs hM hπΔ hEΔ hπu
    (Units.inv_mul w) hQ hu'Δ hu.val_inv_mul (by rw [hgam]; exact hγ) (h5a c)
    (fun y hy => ninLamPf_local ((HW l).W K 1 LL hG) T _ h' w hs hw h5b c hy) (h4W T hcry)
    hpt (hP l hl K LL hG T h' hh' hcry hjmp)

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLI

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

theorem expS_neg (ζ : LL) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) {i : ℤ} (hi : i < 0) :
    expS W T c ζ a y i = 0 := by
  simp [expS, serC, if_neg (show ¬ (0 ≤ i) by omega)]

theorem ind_fil (τ : K →ₐ[Qp] LL) (U : PowerSeries LL) (hU : PowerSeries.constantCoeff U ≠ 0)
    {g : ℤ → T.V ⊗[Qp] BdR} {m₀ : ℤ} (hg : MLG.Bdd g m₀)
    (hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j)) :
    ∀ j, g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
  have key : ∀ N : ℕ, ∀ j, j < m₀ + N → g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro N
    induction N with
    | zero => intro j hj; rw [hg j (by omega)]; exact Submodule.zero_mem _
    | succ N ih =>
      intro j hj
      by_cases hjN : j < m₀ + N
      · exact ih j hjN
      · have hj' : j = m₀ + N := by push_cast at hj; omega
        have hs := hH j
        rw [MLG.serMul_eq_sum U hg j ((j - m₀).toNat + 1) le_rfl, Finset.sum_range_succ'] at hs
        have hrest : ∑ k ∈ Finset.range (j - m₀).toNat, PowerSeries.coeff (k + 1) U • g (j - ((k + 1 : ℕ) : ℤ)) ∈
            Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
          refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
          rw [Finset.mem_range] at hk
          exact u3upPf_FilC_anti (PD := PD) T τ (by push_cast; omega) (ih _ (by push_cast; omega))
        have h0 := Submodule.sub_mem _ hs hrest
        rw [add_sub_cancel_left, PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero] at h0
        exact (Submodule.smul_mem_iff _ hU).1 h0
  intro j
  exact key ((j - m₀).toNat + 1) j (by omega)

end Generic

end Formalism.MainNotions.N.Ln34.MLI

end
end
