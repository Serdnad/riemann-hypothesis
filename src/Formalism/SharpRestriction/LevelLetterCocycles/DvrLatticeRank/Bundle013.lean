module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle009
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle004
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle025
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle011
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle010
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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

@[expose] public section

section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lattice_finrank {O LL V : Type*} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) [Module.Free O T] [Module.Finite O T]
    (hspan : Submodule.span LL (T : Set V) = ⊤) : finrank O T = finrank LL V := by
  classical
  set bT := Module.Free.chooseBasis O T
  set v : Module.Free.ChooseBasisIndex O T → V := fun i => (bT i : V)
  have hli : LinearIndependent O v := bT.linearIndependent.map' T.subtype T.ker_subtype
  have hliLL : LinearIndependent LL v := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hsp : Submodule.span LL (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun x hx => ?_
    have e : x = ∑ i, bT.repr ⟨x, hx⟩ i • v i := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, ← bT.sum_repr ⟨x, hx⟩]
      rw [Submodule.coe_sum]
      rfl
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_top LL V, ← hsp, finrank_span_eq_card hliLL]

set_option maxHeartbeats 1000000 in
theorem r_eq (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (r : ℕ)
    (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) : r = finrank ↥LL.1 T.V := by
  classical
  have : IsFractionRing ↥(OL LL) ↥LL.1 := GenPf.isFractionRing LL
  set W := (HW l).W K 1 LL hG
  have hs : W.s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, hbe⟩, -⟩, -⟩ :=
    (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)
  obtain ⟨-, huniq, ⟨w₁, hw₁⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  obtain ⟨bL0⟩ := MQ.basis_L W T π' (sK l K) hsK w₁ hw₁ huniq b hbΔ hbu hbe c
  have h1 : r = r0 := by
    have e1 := Module.finrank_eq_card_basis bL
    have e2 := Module.finrank_eq_card_basis bL0
    simp only [Fintype.card_fin] at e1 e2
    omega

  have hli : LinearIndependent (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := hbu 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (Set.range fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := hbu x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hbΔ j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := IsBaseChange.basis bN (W.N_base T hT)
  have : Nontrivial W.EE := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 0 =
        algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 1 := by rw [map_zero, map_one]; exact h
    have h0 := congrFun (W.EE_inj h') 0
    exact zero_ne_one h0
  have h2 : r0 = finrank W.EE (W.DD T) := by
    rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]
  have h3 := (W.DD_free T).2
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  rw [h1, h2, h3]
  exact lattice_finrank T.L.T T.L.span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules


set_option maxHeartbeats 1000000 in
theorem invLiftCondition : InvLiftStep := by
  set_option synthInstance.maxHeartbeats 400000 in
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hπ T h' hh' hT hJ c
  haveI := ((HW l).W K 1 LL hG).ddTowO T
  have hNL : NinLam ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' :=
    ninlam_pf D HW F Cm CA CB CK hA l hl K LL hG π' E hπ T h' hT hJ
  rcases le_or_gt (MK l K h') 1 with hM | hM
  · refine ⟨fun w hw => ⟨((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h' • w, ?_, ?_⟩,
      fun wb _ hwb => gradNPf_PiNS_anti _ T π' hM hwb⟩
    · obtain ⟨hwL, hwγ⟩ := (mem_InvS _ T π' _ h' 1 c w).1 hw
      refine (mem_InvS _ T π' _ h' _ c _).2 ⟨Submodule.smul_mem _ _ hwL, ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ (gradNPf_PiNS_anti _ T π' hM hwγ)
    · rw [sub_self]
      exact Submodule.zero_mem _
  have hs : 1 ≤ sK l K := by
    by_contra h0
    have h0' : sK l K = 0 := by omega
    have : MK l K h' = 0 := by simp [MK, h0']
    omega
  obtain ⟨f, t, x, u, hu, hxu, hf, ht, hEE, hπΔ, hγN, hK, hprod⟩ :=
    gradNPf_hyps D HW F Cm hA.1 l hl K LL hG π' E hπ T hT hs
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨a, ha⟩ := hprod (MK l K h' - 1)
  have hM1 : MK l K h' - 1 + 1 = MK l K h' := by omega
  rw [hM1] at ha
  have hσ : sigA l (sK l K) h' = MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial := rfl

  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h0
    have hv := (D.loc l).v_l LL
    rw [h0, AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hℓ : ∀ c : ↥(OL LL), (l : ↥(OL LL)) * c = 0 → c = 0 := by
    intro c hc
    have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) hc
    rw [map_mul, map_natCast, map_zero] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left hl0
    exact (injective_iff_map_eq_zero (algebraMap ↥(OL LL) ↥LL.1)).1 Subtype.val_injective c h2

  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨⟨r, b, hbΔ, huniq, -⟩, -⟩ := hm₀
  obtain ⟨w, hw⟩ := hπ.2.2.1
  have hnz : ∀ y : ℕ, 1 ≤ y → y < MK l K h' → ∀ r₀ ∈ ((HW l).W K 1 LL hG).N T,
      ∀ d ∈ ((HW l).W K 1 LL hG).N T, ((x ^ sK l K) ^ y - 1) • r₀ = π' • d →
      ∃ e ∈ ((HW l).W K 1 LL hG).N T, r₀ = π' • e := by
    intro y hy1 hyM r₀ hr₀ d hd hrd
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun y => (x ^ sK l K) ^ y - 1)
      (Finset.mem_Ico.2 ⟨hy1, hyM⟩)
    rw [hq] at ha
    refine invLiftPf_nzd _ T π' w (sK l K) w.isUnit hw (l : ↥(OL LL)) hℓ r b
      (fun j => (hbΔ j).1) huniq (MK l K h' - 1 + padicValNat l (MK l K h' - 1).factorial) r₀
      ((a * q) • d) hr₀ ?_ ?_
    · rw [← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))]
      exact Submodule.smul_mem _ _ hd
    · rw [ha, mul_comm ((x ^ sK l K) ^ y - 1) q, ← mul_assoc, mul_smul, hrd,
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) (π' • d),
        ← algebraMap_smul (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (a * q) d, smul_smul, smul_smul,
        mul_comm]
  have hpσ : (((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ^ sigA l (sK l K) h') =
      a * ∏ y ∈ Finset.Ico 1 (MK l K h'), ((x ^ sK l K) ^ y - 1) := by
    rw [hpl, hσ]
    exact ha
  have hGr : GradN ((HW l).W K 1 LL hG) T π' (sigA l (sK l K) h') (MK l K h') :=
    gradNPf_local _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ _ (by omega) a hpσ
  refine ⟨invLiftPf_lift _ T π' _ h' _ _ c hGr hNL, fun wb hwb hwb1 => ?_⟩
  exact invLiftPf_inj _ T π' f t (x ^ sK l K) hf ht hEE hπΔ hγN hK _ hnz wb hwb1
    ((mem_InvS _ T π' _ h' _ c wb).1 hwb).2

end Formalism.MainNotions.N.Ln34

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem exponent_recursion_of_dimension (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm) (h8 : Formalism.MainNotions.ElementDenominator.adm8 D)
    (hdim : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ≤
          finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ)) :
    ExpansionFormAll D HW := by
  intro l _ hl K LL hG T h' hh' hT hJ c y _ hyc hk hexp
  obtain ⟨p1, -, p3, p4, p5, -⟩ := h1 l K 1 LL hG
  obtain ⟨⟨hfc, -⟩, hfd⟩ := h8 l K LL T
  have hFr : IsFractionRing ↥(OL LL) ↥LL.1 := by
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : FiniteDimensional ↥LL.1
      ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
    Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
  haveI : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
    infer_instance
  have hyc' : (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have h := LinearMap.mem_ker.1 hyc
    simpa only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using h
  refine mem_N_of_exp ((HW l).W K 1 LL hG) hFr ((HW l).W_s K 1 LL hG) T
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (M := fun _ => h') (h := fun _ => h') (p1 T hT) (p3 T hT)
    (p4 T hT) (p5 T _ _ hT fun τ _ _ => hJ τ) c (fun ζ hζ => ?_) (fun τ => (hfd τ).1)
    (hdim l K LL hG T hT c) y hyc' hk hexp
  rw [(D.loc l).PD_p] at hζ
  exact exists_pt D HW hG c ζ hζ

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem FilC_succ_le (τ : K →ₐ[Qp] LL) (a : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (a + 1) ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a := by
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (ExtPf.extPf_fildR_succ_le PD T.ρ τ a) _

theorem FilC_anti (τ : K →ₐ[Qp] LL) : Antitone fun a => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a :=
  antitone_int_of_succ_le (fun a => FilC_succ_le T τ a)

theorem FilC_mono_shift (τ : K →ₐ[Qp] LL) (b : ℤ) :
    Monotone fun i : ℤ => Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b - i) :=
  fun i j hij => FilC_anti T τ (by omega : b - j ≤ b - i)

theorem FilC_top (τ : K →ₐ[Qp] LL) (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) (b : ℤ) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ b ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rcases le_or_gt (-(h' : ℤ)) b with hb | hb
  · exact FilC_anti T τ hb
  · have key : ∀ d : ℕ, FildR PD T.ρ τ (-(h' : ℤ) - (d : ℤ)) = FildR PD T.ρ τ (-(h' : ℤ)) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
        rw [← ih]
        have hnj : ¬ IsJumpV PD T.ρ τ (-(h' : ℤ) - ((d + 1 : ℕ) : ℤ)) := fun hJ => by
          have := (hj _ hJ).1
          push_cast at this
          omega
        unfold IsJumpV at hnj
        rw [not_not] at hnj
        have e : -(h' : ℤ) - ((d + 1 : ℕ) : ℤ) + 1 = -(h' : ℤ) - (d : ℤ) := by push_cast; ring
        rw [e] at hnj
        exact hnj.symm
    have := key ((-(h' : ℤ) - b).toNat)
    rw [show -(h' : ℤ) - (((-(h' : ℤ) - b).toNat : ℕ) : ℤ) = b by omega] at this
    unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
    rw [this]

include W in
theorem p_ne_zero : (PD.p : LL) ≠ 0 := by
  intro h
  have := W.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem pow_vanish (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ)
    (a : PowerSeries LL) : ∀ j < m, PowerSeries.coeff j (g ^ m * a) = 0 := by
  intro j hj
  have hX : (PowerSeries.X : PowerSeries LL) ∣ g := PowerSeries.X_dvd_iff.mpr hg
  obtain ⟨h, hh⟩ := pow_dvd_pow_of_dvd hX m
  rw [hh, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem pow_vanish' (g : PowerSeries LL) (hg : PowerSeries.constantCoeff g = 0) (m : ℕ) :
    ∀ j < m, PowerSeries.coeff j (g ^ m) = 0 := by
  intro j hj
  simpa using pow_vanish g hg m 1 j hj

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_fil (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k) := by
  rw [← levN_letE]
  exact (hp4.2 c ζ τ hPt).2.1 x k

theorem ιDi_le_top (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hj : JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h')) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)) := by
  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  exact FilC_top T h' τ hj _ (Submodule.mem_inf.1 (levN_fil W T c hp4 hPt ⟨_, hk⟩ k)).2

theorem valAt_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    {x : W.DD T} (hx : x ∈ W.N T) : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  classical
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ _ (Nat.find_spec h) _).1
  · exact Submodule.zero_mem _

theorem expS_mem (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ) {m : ℕ}
    (a : Fin m → LetA O n) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ W.N T) (i : ℤ) :
    expS W T c ζ a y i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c := by
  unfold expS serC
  refine Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (valAt_mem W T c hp4 hPt (hy j))
  · exact Submodule.zero_mem _

theorem levE_zero (hs : W.s = 1) {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev c ζ Eπ) = 0 := by
  have h0 := (levQ_pt W hs c ζ hζ hζ1).1
  have hw : PowerSeries.constantCoeff (W.lev c ζ w') * PowerSeries.constantCoeff (W.lev c ζ w) = 1 := by
    rw [← map_mul, ← map_mul, hww, map_one, map_one]
  rw [hQ, map_mul, map_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · rw [h, mul_zero] at hw
    exact absurd hw zero_ne_one
  · exact h

end Exp

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end
