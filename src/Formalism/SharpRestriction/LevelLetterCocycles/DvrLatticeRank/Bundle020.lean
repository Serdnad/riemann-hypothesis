module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle023
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle021
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle026
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle012
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle015
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle013
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle008
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3downPfFildRConst
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle017
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalFiltrationHolds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries


open Formalism.MainNotions.N.Ln34.ModelFPf in
theorem universal_lift_ring_membership (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ ∧ π' ∈ ((HW l).W K 1 LL hG).AΔ ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    (∃ uE ∈ ((HW l).W K 1 LL hG).AΔ, ∃ uE' ∈ ((HW l).W K 1 LL hG).AΔ, uE' * uE = 1 ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = uE * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ∧
    (∃ uπ ∈ ((HW l).W K 1 LL hG).AΔ, ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * uπ) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
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
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  have hEu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw, map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hnzπ : ∀ a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)), a * π' = 0 → a = 0 := by
    intro a ha
    apply ((HW l).W K 1 LL hG).EE_inj
    have h1 := congrArg (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE) ha
    rw [map_mul, map_zero] at h1
    rw [map_zero]
    exact hπu.mul_left_eq_zero.1 h1
  have hγπ : ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' =
      (1 + (w2 : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') * π' := by
    rw [sub_eq_iff_eq_add] at hw2
    rw [hw2]
    ring
  exact ⟨hEΔ, hπΔ, hEu, hπu, ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl),
    ⟨u, huΔ, _, hu'Δ, hu.val_inv_mul, hγ⟩,
    ⟨_, u_mem_AΔ ((HW l).W K 1 LL hG) hπΔ hnzπ hγπ, by rw [hγπ]; ring⟩⟩

theorem universal_lift_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 ∧
    coeff 1 (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ≠ 0 ∧
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ π') ≠ 0 ∧
    ∀ a, ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam a) =
      rescale (algebraMap ↥(OL LL) ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.uU ((HW l).W K 1 LL hG) : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hζ : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hp]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨-, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, -, -⟩ := hp9
  obtain ⟨e₁, he₁, he₁0⟩ :=
    DescentValuation.u3downPf_lev_E ((HW l).W K 1 LL hG) c ζ hζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w hw
  refine ⟨?_, ?_, DescentValuation.u3downPf_cc_π' ((HW l).W K 1 LL hG) c ζ hζ π' (sK l K) w0 hw0, ?_⟩
  · rw [he₁]
    simp
  · rw [he₁, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact he₁0
  · intro a
    have hg := ((HW l).W K 1 LL hG).gam_gen
    exact ((Cm l).C K 1 LL hG).tie.lev_Γ _ c ζ ζ 1 1 (by rw [pow_one]; exact hζ)
      (le_of_eq (by simpa [hs] using hg.symm)) (pow_one ζ).symm a

theorem embeddings_card_le_degree (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ τs : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1), (∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → τ ∈ τs) ∧
      τs.card ≤ finrank ↥(K0 K) ↥K.1 := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    apply Nat.finite_of_card_ne_zero
    rw [GenPf.natCard_emb K LL hG]
    exact (Module.finrank_pos (R := ℚ_[l]) (M := ↥K.1)).ne'
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  haveI : FiniteDimensional ↥(K0 K) ↥K.1 := Module.Finite.right ℚ_[l] ↥(K0 K) ↥K.1
  refine ⟨Finset.univ.filter (fun τ => Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c),
    fun τ ζ hpt => Finset.mem_filter.2 ⟨Finset.mem_univ _, u3upPf_pt_over D HW hG c ζ τ hpt⟩, ?_⟩
  have h := kapPiPf_card ((HW l).W K 1 LL hG) c
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.DescentValuation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct
open Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.UnivLinkPf

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3downPf_map_NcS {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (h1 : IsCrys PD T₁.ρ)
    (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁} (hx : x ∈ NcS W T₁ c) : W.map F x ∈ NcS W T₂ c := by
  rw [mem_NcS] at hx ⊢
  exact ⟨W.map_N F h1 h2 x hx.1, univLinkPf_map_DelS W F hx.2.1, by rw [← map_letA_smul, hx.2.2]⟩

theorem u3downPf_mkL_eq (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) {x z : W.DD T}
    (hx : x ∈ NcS W T (c - 1)) (hz : z ∈ NcS W T (c - 1)) (r : O) (h : z - r • x ∈ PiNS W T π' 1) :
    mkL W T π' c z hz = r • mkL W T π' c x hx := by
  unfold mkL
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  simpa using h

theorem u3downPf_core {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ S ρ : ℕ}
    {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ} {c : ZMod n}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hfr : IsFrame W Pt π' Eπ h' M σ c α β) (hc1 : IsCrys PD T₁.ρ) (hc2 : IsCrys PD T₂.ρ)
    (hj1 : ∀ τ, JumpsInV PD T₁.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hj2 : ∀ τ, JumpsInV PD T₂.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (hMF1 : ModelF W T₁ Pt π' Eπ h' M c α β) (hMF2 : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)
    (hK : ModelK W F π' ρ c)
    (hC1 : ∀ x (hx : x ∈ NcS W T₁ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₁ π' c x hx ∈ InvL W T₁ Pt π' Eπ h' c ⊤)
    (hC2 : ∀ x (hx : x ∈ NcS W T₂ (c - 1)) f, IsCoord W Pt π' Eπ h' S up b c f →
      f ⊗ₜ mkL W T₂ π' c x hx ∈ InvL W T₂ Pt π' Eπ h' c ⊤) :
    ThirdPropositionSlot W F Pt π' Eπ h' M S up b c ρ α := by
  intro f hf x hx _ h1 y hy hα
  obtain ⟨x₁, hx₁, hdiff⟩ := hK x hx
  have hyI : y ∈ InvS W T₂ π' Eπ h' 1 c := hMF2.2.2.2.1 _ h1 y hy hα (hC2 x hx f hf)
  have hI1 := hC1 x₁ hx₁ f hf
  have hL1 : f ⊗ₜ mkL W T₁ π' c x₁ hx₁ ∈ LamLA W T₁ π' Eπ h' c ⊤ := (Submodule.mem_inf.1 hI1).1
  obtain ⟨w₁, hw₁⟩ := Submodule.Quotient.mk_surjective _ (α T₁ ⟨_, hL1⟩)
  have hw₁I : (w₁ : W.DD T₁) ∈ InvS W T₁ π' Eπ h' 1 c := hMF1.2.2.2.1 _ hL1 w₁ w₁.2 hw₁.symm hI1
  have hmx : W.map F x₁ ∈ NcS W T₂ (c - 1) := u3downPf_map_NcS W F hc1 hc2 (c - 1) hx₁
  have hL2 : f ⊗ₜ mkL W T₂ π' c (W.map F x₁) hmx ∈ LamLA W T₂ π' Eπ h' c ⊤ :=
    (Submodule.mem_inf.1 (hC2 _ hmx f hf)).1
  have hy₂ : W.map F (w₁ : W.DD T₁) ∈ LamPS W T₂ Eπ h' c := univLinkPf_map_LamPS W F hc1 hc2 Eπ h' c w₁.2
  have hnat := (hfr.2 T₁ T₂ F hc1 hc2 hj1 hj2).1 _ hL1 _ hL2 _ w₁.2 hy₂
    ⟨1, fun _ => f, fun _ => x₁, fun _ => hx₁, fun _ => hmx, by simp, by simp⟩ hw₁.symm
  have heq : mkL W T₂ π' c (W.map F x₁) hmx = ((PD.p : ℕ) : O) ^ ρ • mkL W T₂ π' c x hx :=
    u3downPf_mkL_eq W T₂ π' c hx hmx _ hdiff
  have hsub : (⟨_, hL2⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = ((PD.p : ℕ) : O) ^ ρ • ⟨_, h1⟩ :=
    Subtype.ext (by simp [heq, TensorProduct.tmul_smul])
  rw [hsub, map_smul, hα] at hnat
  have hJ : Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ ρ • (⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨_, hy₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c) := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hnat
  have hP := univLinkPf_PiNS_anti W T₂ π' hM (univLinkPf_JP W T₂ hMF2 hM _ hJ)
  refine ⟨hyI, w₁, hw₁I, ?_⟩
  simpa using hP

theorem u3downPf_jumps (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (u : Bool) (bt S η h' : ℕ)
    (hj : JumpsInV PD T.ρ τ (deep u bt S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bt) (hbS : bt + S ≤ h') :
    JumpsInV PD T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
  intro a ha
  have h := hj a ha
  unfold deep at h
  split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h ⊢ <;> omega

end Local

section Record

theorem u3downPf_sK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) :
    1 ≤ sK l K := by
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl1 : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have he : 0 < eK K := by
    rcases Nat.eq_zero_or_pos (eK K) with h | h
    · rw [h, zero_dvd_iff] at hd; omega
    · exact h
  exact Nat.div_pos (Nat.le_of_dvd hl1 hd) he

theorem u3downPf_modelK_of_wKill (D : D7) (HW : HWOf D.loc) (hW : wKillR D HW) : modelKR D HW := by
  intro l _ hl K LL hG π' E hp T₁ T₂ F h' _ hc1 hc2 hon hj1 c y hy
  obtain ⟨x, hx, hxy⟩ := hW l hl K LL hG π' E hp T₁ T₂ F h' hc1 hc2 hon hj1 (c - 1) y hy
  exact ⟨x, hx, by rw [hxy, sub_self]; exact Submodule.zero_mem _⟩

theorem u3downPf_lemC_rec (D : D7) (HW : HWOf D.loc) (Fo : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW Fo) (h1 : adm1 D HW Fo Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (S η h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hc : IsCrys ((D.loc l).PD K) T.ρ)
    (hj : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η))
    (hηb : ∀ τ, η < b τ)
    (hdown : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c → up τ = false) :
    LemC ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' S up b c := by
  intro x hx _ f hf
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w', hw'⟩, -⟩ := hp
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [(D.loc l).PD_p K]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hdown' : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → up τ = false := fun τ ζ hpt =>
    hdown τ (u3upPf_pt_over D HW hG c ζ τ hpt)
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hgk : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [(D.loc l).PD_p K]; exact hl)
  refine u3downPf_lemC ((HW l).W K 1 LL hG) T _ π' _ h' S up b c ?_ ?_ hdown' ?_ ?_ ?_ ?_ ?_ x hx f hf
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  · have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw', map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  · intro τ ζ hpt
    exact u3downPf_cc_π' _ c ζ (hprim τ ζ hpt) π' _ w hw
  · intro τ ζ hpt
    exact u3downPf_lev_E _ c ζ (hprim τ ζ hpt) _ w' hw'
  · intro τ ζ hpt
    refine ⟨algebraMap ↥(OL LL) ↥LL.1 (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)),
      (((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero),
      fun a => ?_⟩
    have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
        (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
      rw [hgk, Nat.cast_one, Nat.cast_one, ((HW l).W K 1 LL hG).gam_gen, hs, Nat.cast_one]
    have h1' : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by rw [pow_one]; exact hprim τ ζ hpt
    have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 h1' hv (by rw [pow_one]) a
    exact this
  · intro x' hx' τ ζ hpt
    exact u3downPf_valAt_fil _ T c ζ τ (((h1 l K 1 LL hG).2.2.2.1 T hc).2 c ζ τ hpt).2.1 x' hx'
  · intro τ ζ hpt a hJ
    have h := hj τ a hJ
    have hd := hdown' τ ζ hpt
    have hb := hηb τ
    unfold deep at h
    rw [if_neg (by simp [hd])] at h
    simp only [Set.mem_union, Set.mem_Icc] at h
    omega

theorem u3downPf_link (hW : WStep) : DownSlotOfModels := by
  intro D HW Fo Cm CA CB CK hA hMF l _ hl K LL hG π' E hp T₁ T₂ F S η m h' up b c α β hfr hN hdown
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hJ1 : ∀ τ, JumpsInV ((D.loc l).PD K) T₁.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₁ τ (up τ) (b τ) S η h' (hj1 τ) (hηb τ) (hbS τ)
  have hJ2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := fun τ =>
    u3downPf_jumps T₂ τ (up τ) (b τ) S η h' (hj2 τ) (hηb τ) (hbS τ)
  have hM : 1 ≤ MK l K h' :=
    Formalism.MainNotions.N.Ln34.ClassMapPf.classMapPf_MK_pos K h' hh' (u3downPf_sK_pos hl K LL hG)
  have hF' := hMF l hl K LL hG π' E hp h' hh' c α β hfr
  have hK' := u3downPf_modelK_of_wKill D HW (hW D HW Fo Cm CA CB CK hA) l hl K LL hG π' E hp
    T₁ T₂ F h' hh' hc1 hc2 hon hJ1 c
  refine u3downPf_core ((HW l).W K 1 LL hG) F hfr hc1 hc2 hJ1 hJ2 (hF' T₁ hc1 hJ1) (hF' T₂ hc2 hJ2)
    hM hK' ?_ ?_
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₁ S η h' up b c hc1 hj1 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf
  · intro x hx f hf
    exact u3downPf_lemC_rec D HW Fo Cm hA.1 hl K LL hG π' E hp T₂ S η h' up b c hc2 hj2 hηb hdown x hx
      (fun τ hτ hup => by simp [hdown τ hτ] at hup) f hf

end Record

theorem down_of_models : Formalism.MainNotions.N.Ln34.DownSlotOfModels := u3downPf_link Formalism.MainNotions.N.Ln34.w_pf

end Formalism.MainNotions.N.Ln34.DescentValuation
end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLH

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

theorem γLA_smulLA (b : LetA O n) (z : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c b z) = smulLA W T π' c (W.γA W.gamK b) (γLA W T π' c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    show W.γE W.gamK (algebraMap (LetA O n) W.EE b * e) ⊗ₜ s =
      (algebraMap (LetA O n) W.EE (W.γA W.gamK b) * W.γE W.gamK e) ⊗ₜ s
    rw [map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem γA_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA W.gamK a ∈ W.AΔ := by
  intro δ hδ
  have e1 : W.γA δ (W.γA W.gamK a) = W.γA (δ * W.gamK) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  have e2 : W.γA W.gamK (W.γA δ a) = W.γA (W.gamK * δ) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  rw [e1, mul_comm, ← e2, ha δ hδ]

theorem rep_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (hr : IsRepL W T π' Eπ h' c x a y) :
    IsRepL W T π' Eπ h' c (γLA W T π' c x)
      (fun j => ⟨u₀ * W.γA W.gamK (a j), W.AΔ.mul_mem hu₀ (γA_mem_AΔ W (a j).2)⟩) y := by
  obtain ⟨hy, hx⟩ := hr
  refine ⟨hy, ?_⟩
  have e : smulLA W T π' c (Eπ ^ h') (γLA W T π' c x) =
      smulLA W T π' c u₀ (γLA W T π' c (smulLA W T π' c (Eπ ^ h') x)) := by
    rw [γLA_smulLA, MLE.smulLA_smulLA, hΛ]

  rw [e, hx, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show (algebraMap (LetA O n) W.EE u₀ * W.γE W.gamK (algebraMap (LetA O n) W.EE
      ((letE c : LetA O n) * a j))) ⊗ₜ mkL W T π' c (y j) (hy j) = _
  rw [W.γE_ext, ← map_mul]
  congr 2
  show u₀ * W.γA W.gamK ((letE c : LetA O n) * a j) = (letE c : LetA O n) * (u₀ * W.γA W.gamK (a j))
  rw [map_mul, hlet]
  ring

theorem expS_γ (ζ : LL) (u : LL) (hlev : ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => W.γA W.gamK (a j)) y i = u ^ i.toNat • expS W T c ζ a y i := by
  simp only [expS, serC, hlev, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [PowerSeries.coeff_rescale, mul_smul]
  · rw [smul_zero]

theorem nl_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c) (u : LL)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) : γLA W T π' c x ∈ NL W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, hr, hg⟩ := hx
    refine Submodule.subset_span ⟨m, _, y, rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr, fun τ ζ hpt => ?_⟩
    refine MLB.goodF_mul W T c ζ τ h' u₀ (fun j => W.γA W.gamK (a j)) y (fun i => ?_)
    rw [expS_γ W T c ζ u (hlev τ ζ hpt)]
    exact Submodule.smul_mem _ _ (hg τ ζ hpt i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

end Generic

end Formalism.MainNotions.N.Ln34.MLH

end
end

section

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

theorem universal_lift_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) (hdR : DdRFull D) (hDi : DiRank D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (r : ℕ) (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) (rep : Fin r → ((HW l).W K 1 LL hG).DD T)
    (hrep : ∀ k, rep k ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) (hbrep : ∀ k, bL k = mkL ((HW l).W K 1 LL hG) T π' c (rep k) (hrep k))
    (S η m : ℕ) (upτ : Bool) (bτ : ℕ)
    (hj : JumpsInV ((D.loc l).PD K) T.ρ τ (deep upτ bτ S ∪ Set.Icc (-(η : ℤ)) η)) (hηb : η < bτ)
    (hm : ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV ((D.loc l).PD K) T.ρ τ a ≤ m) :
    (upτ = true →
      (∀ i : ℤ, i < -((bτ : ℤ) + S) → ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-i) → d = 0) ∧
      r ≤ finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ bτ).comap (Phi ((HW l).W K 1 LL hG) T c ζ rep)) + m) ∧
    (upτ = false →
      finrank ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(bτ : ℤ) + 1)).comap
        (Phi ((HW l).W K 1 LL hG) T c ζ rep)) ≤ m ∧
      ∀ d : Fin r → ↥LL.1,
        Phi ((HW l).W K 1 LL hG) T c ζ rep d ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-((bτ : ℤ) + S))) := by
  exact UniversalFiltration.universal_filtration_holds D HW F Cm hA hdR hDi hl K LL hG π' E hp9 T hT c τ ζ hpt r bL rep hrep hbrep
    S η m upτ bτ hj hηb hm

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
