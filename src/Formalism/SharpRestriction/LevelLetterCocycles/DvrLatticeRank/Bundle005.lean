module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle014
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdOfCoeffSubstXPowNeZero
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfBSingleMem
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfGoodExtensions

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MQ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

theorem dvd_pow_of_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : O) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit p) : ∀ a : O, a ≠ 0 → ∃ (k : ℕ) (b : O), p ^ k = b * a := by
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hpu (associated_one_iff_isUnit.1 (by simpa using hk))
  have h1 : ϖ ^ m ∣ ϖ ^ (k * m) := pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk1))
  have hdvd : a ∣ p ^ m :=
    hm.dvd.trans (h1.trans (by rw [pow_mul]; exact (hk.symm.pow_pow).dvd))
  obtain ⟨b, hb⟩ := hdvd
  exact ⟨m, b, by rw [hb, mul_comm]⟩

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem mem_DelS' {x : W.DD T} : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  simp [DelS, Submodule.mem_iInf, sub_eq_zero]

theorem mem_letS' {c : ZMod n} {x : W.DD T} : x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  simp [letS, sub_eq_zero]

theorem γD_smulA' (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem expand_at (π' a : LetA O n) (i : ZMod n) (hπ0 : PowerSeries.constantCoeff (π' i) = 0)
    (F : PowerSeries O) (hF : a i = PowerSeries.subst (π' i) F) :
    a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) +
      PowerSeries.C (PowerSeries.constantCoeff F) := by
  have hS : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' hπ0
  conv_lhs => rw [hF, PowerSeries.eq_X_mul_shift_add_const F]
  rw [PowerSeries.subst_add hS, PowerSeries.subst_mul hS, PowerSeries.subst_X hS, PowerSeries.subst_C]
  rfl



theorem basis_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Nonempty (Module.Basis (Fin r) O (LcQ W T π' c)) := by
  classical
  set d : ZMod n := c - 1 with hd
  have hπd : ∀ i, π' i = (w₁ : LetA O n) i * PowerSeries.X ^ s' := fun i => π_at s' π' w₁ hπ i
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hπd i, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hmem : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T d := by
    intro j
    obtain ⟨hN, hΔ⟩ := hbΔ j
    refine ⟨⟨(W.N T).smul_mem _ hN, (mem_DelS' W T).2 fun δ hδ => ?_⟩, (mem_letS' W T).2 ?_⟩
    · rw [γD_smulA', hΔ δ hδ, (show ∀ δ ∈ W.DelF, W.γA δ (letE d : LetA O n) = letE d from letE_mem W d) δ hδ]
    · rw [smul_smul, letE_mul_self']
  let v : Fin r → LcQ W T π' c := fun j => Submodule.Quotient.mk ⟨_, hmem j⟩
  have hli : LinearIndependent O v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (∑ j, g j • (⟨_, hmem j⟩ : ↥(NcS W T d))) ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by

      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      simpa only [map_smul, Submodule.mkQ_apply] using hg
    rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sum] at h0
    simp only [Submodule.coe_smul] at h0
    obtain ⟨⟨y, hyN, hy⟩, -⟩ := h0
    obtain ⟨a', ha'⟩ := (hbu y hyN).exists
    have hxN : π' • y ∈ W.N T := (W.N T).smul_mem _ hyN
    have hrep1 : π' • y = ∑ j, (π' * a' j) • b j := by
      rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    have hrep2 : π' • y = ∑ j, (algebraMap O (LetA O n) (g j) * (letE d : LetA O n)) • b j := by
      have hy' : π' • y = ∑ j, g j • ((letE d : LetA O n) • b j) := by
        rw [← hy]
        show π' • y = ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y
        rw [pow_one]
        rfl
      rw [hy']
      exact Finset.sum_congr rfl fun j _ => by rw [← smul_smul, algebraMap_smul]
    have huq := (hbu _ hxN).unique hrep1 hrep2
    have hj := congrFun (congrFun huq j) d
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, mul_one] at hj
    have hcc := congrArg PowerSeries.constantCoeff hj
    rw [map_mul, hπ0 d, zero_mul] at hcc
    have : PowerSeries.constantCoeff ((algebraMap O (LetA O n) (g j)) d) = g j := by
      show PowerSeries.constantCoeff (algebraMap O (PowerSeries O) (g j)) = g j
      rw [PowerSeries.algebraMap_apply]
      simp
    rw [this] at hcc
    exact hcc.symm
  have hsp : ⊤ ≤ Submodule.span O (Set.range v) := by
    rintro q -
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨⟨hxN, hxΔ⟩, hxl⟩ := hx
    have hxΔ' := (mem_DelS' W T).1 hxΔ
    have hxl' := (mem_letS' W T).1 hxl
    obtain ⟨a, haΔ, hxa⟩ := hbe x ⟨hxN, hxΔ'⟩
    choose F hF using fun j => (huniq (a j) (haΔ j)).exists
    let κ : Fin r → O := fun j => PowerSeries.constantCoeff (F j d)
    let t : Fin r → LetA O n := fun j _ => PowerSeries.subst (π' d) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F j d))
    have hkey : ∀ j, (letE d : LetA O n) * a j = algebraMap O (LetA O n) (κ j) * letE d + π' * ((letE d : LetA O n) * t j) := by
      intro j
      funext i
      by_cases hi : i = d
      · subst hi
        simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_eq_same, one_mul, mul_one]
        rw [expand_at π' (a j) _ (hπ0 _) (F j _) (hF j _)]
        show _ = algebraMap O (PowerSeries O) (κ j) + _
        rw [PowerSeries.algebraMap_apply]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, t, κ]
        ring
      · simp [letE, Pi.single_apply, hi]
    set y : W.DD T := ∑ j, ((letE d : LetA O n) * t j) • b j with hydef
    have hyN : y ∈ W.N T := Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbΔ j).1
    have hxe : x = ∑ j, κ j • ((letE d : LetA O n) • b j) + π' • y := by
      conv_lhs => rw [← hxl', hxa, Finset.smul_sum]
      rw [hydef, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, hkey j, add_smul, smul_smul, ← algebraMap_smul (LetA O n) (κ j), smul_smul]
    have hdiff : (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) - ∑ j, κ j • ⟨_, hmem j⟩ ∈
        (PiNS W T π' 1).comap (NcS W T d).subtype := by
      rw [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have he : x - ∑ j, κ j • ((letE d : LetA O n) • b j) = π' • y := by rw [hxe]; abel
      rw [he]
      refine ⟨⟨y, hyN, ?_⟩, ?_⟩
      · show ((π' ^ 1 : LetA O n) • LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T) y = π' • y
        rw [pow_one]; rfl
      · rw [← he]
        refine sub_mem hxΔ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j).1.2)
    have hq : (Submodule.Quotient.mk (⟨x, ⟨⟨hxN, hxΔ⟩, hxl⟩⟩ : ↥(NcS W T d)) : LcQ W T π' c) = ∑ j, κ j • v j := by

      rw [(Submodule.Quotient.eq _).2 hdiff, ← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply]
      rfl
    rw [hq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp⟩

theorem finite_L [IsDomain O] (π' : LetA O n) (s' : ℕ) (hs : 1 ≤ s') (w₁ : (LetA O n)ˣ)
    (hπ : π' = w₁ * (letπ : LetA O n) ^ s')
    (huniq : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O, ∀ i, a i = PowerSeries.subst (π' i) (f i))
    {r : ℕ} (b : Fin r → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (hbe : ∀ x ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧ x = ∑ j, a j • b j)
    (c : ZMod n) : Module.Finite O (LcQ W T π' c) := by
  exact Module.Finite.of_basis (basis_L W T π' s' hs w₁ hπ huniq b hbΔ hbu hbe c).some

end Formalism.MainNotions.N.Ln34.MQ
end
end

section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2C

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem constantCoeff_uniformiser_zero {s' : ℕ} {π' : LetA O n} (w : (LetA O n)ˣ) (hw : π' = (w : LetA O n) * letπ ^ s')
    (hs : 1 ≤ s') (i : ZMod n) : PowerSeries.constantCoeff (π' i) = 0 := by
  have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]

theorem u2ringPfC_subΔ {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) :
    ∀ δ ∈ W.DelF, ∀ i (F : PowerSeries O),
      W.γ₀ δ (PowerSeries.subst (π' i) F) = PowerSeries.subst (π' i) F := by
  intro δ hδ i F
  rw [DualFramesAlt.EigenUniformiser.algHom_subst (W.γ₀ δ) (W.γ₀_X δ).1 (hπ0 i)]
  congr 1
  exact congrFun (hπΔ δ hδ) i

theorem u2ringPfC_inj {π' : LetA O n} (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i))
    (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0) (c : ZMod n) (F F' : PowerSeries O)
    (hFF : PowerSeries.subst (π' c) F = PowerSeries.subst (π' c) F') : F = F' := by
  have hsub0 : ∀ i, PowerSeries.subst (π' i) (0 : PowerSeries O) = 0 := fun i => by
    rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)), map_zero]
  have hmem := u2ringPfB_single_mem W c (PowerSeries.subst (π' c) F)
    (fun δ hδ => u2ringPfC_subΔ W hπΔ hπ0 δ hδ c F)
  obtain ⟨f, -, huniq⟩ := hsub _ hmem
  have key : ∀ H, PowerSeries.subst (π' c) H = PowerSeries.subst (π' c) F →
      (Pi.single c H : ZMod n → PowerSeries O) = f := fun H hH => huniq _ (fun i => by
    by_cases hi : i = c
    · subst hi; simp only [Pi.single_eq_same]; exact hH.symm
    · simp only [Pi.single_eq_of_ne hi, hsub0])
  have := congrFun ((key F rfl).trans (key F' hFF.symm).symm) c
  simpa using this

theorem u2ringPfC_pre {π' : LetA O n}
    (hsub : ∀ a, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W a → ∃! f : ZMod n → PowerSeries O,
      ∀ i, a i = PowerSeries.subst (π' i) (f i)) (c : ZMod n) (x : PowerSeries O)
    (hx : ∀ δ ∈ W.DelF, W.γ₀ δ x = x) : ∃ F : PowerSeries O, PowerSeries.subst (π' c) F = x := by
  obtain ⟨f, hf, -⟩ := hsub _ (u2ringPfB_single_mem W c x hx)
  refine ⟨f c, ?_⟩
  have := hf c
  simp only [Pi.single_eq_same] at this
  exact this.symm

theorem u2ringPfC_nu [IsDomain O] [CharZero O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hK : W.gamK = W.gam) (h' : ℕ) :
    ∃ ν : LetA O n, ν ∈ W.AΔ ∧
      ν * W.γA W.gamK (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  obtain ⟨hπΔ, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, ⟨w₂, hγ⟩, -⟩ := hR
  have hπ0 := constantCoeff_uniformiser_zero w hw hs
  set Ê := Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hÊdef
  have hq₀ := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hÊ0 : ∀ i, Ê i ≠ 0 := by
    intro i h
    apply hq₀
    have e1 : W.q₀ = (w₁ : LetA O n) i * Ê i := congrFun hq i
    rw [e1, h, mul_zero]
  have hπΔ' : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (π' i) = π' i := fun δ hδ i => congrFun (hπΔ δ hδ) i
  have hÊΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (Ê i) = Ê i := by
    intro δ hδ i
    show W.γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply, hπΔ' δ hδ i]
  have hU : ∀ i, ∃ u : PowerSeries O, IsUnit u ∧ W.γ₀ W.gam (Ê i) = Ê i * u := by
    intro i
    have hγi : W.γ₀ W.gam (π' i) - π' i = (w₂ : LetA O n) i * π' i * Ê i := congrFun hγ i
    obtain ⟨D, hD⟩ := Polynomial.sub_dvd_eval_sub (W.γ₀ W.gam (π' i)) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨1 + (w₂ : LetA O n) i * π' i * D, ?_, ?_⟩
    · rw [PowerSeries.isUnit_iff_constantCoeff]
      simp [hπ0 i]
    · have e2 : W.γ₀ W.gam (Ê i) = Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) :=
        (Polynomial.aeval_algHom_apply (W.γ₀ W.gam) (π' i) (E i)).symm
      have e3 : Ê i = Polynomial.aeval (π' i) (E i) := rfl
      have hD' : Polynomial.aeval (W.γ₀ W.gam (π' i)) (E i) - Polynomial.aeval (π' i) (E i) =
          (W.γ₀ W.gam (π' i) - π' i) * D := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.eval₂_eq_eval_map]
        exact hD
      rw [e3] at hγi
      rw [hγi] at hD'
      rw [e2, e3]
      linear_combination hD'
  choose U hUu hUeq using hU
  have hUunit : IsUnit (U : LetA O n) := Pi.isUnit_iff.2 hUu
  set V : LetA O n := ((hUunit.unit⁻¹ : (LetA O n)ˣ) : LetA O n) with hV
  have hVU : V * U = 1 := by rw [hV]; exact hUunit.val_inv_mul
  have hUΔ : ∀ δ ∈ W.DelF, ∀ i, W.γ₀ δ (U i) = U i := by
    intro δ hδ i
    have h1 := congrArg (W.γ₀ δ) (hUeq i)
    rw [u2ringPfB_γ₀_comm, map_mul, hÊΔ δ hδ i, hUeq i] at h1
    exact (mul_left_cancel₀ (hÊ0 i) h1).symm
  refine ⟨V ^ h', ?_, ?_⟩
  · intro δ hδ
    funext i
    show W.γ₀ δ ((V ^ h') i) = (V ^ h') i
    rw [Pi.pow_apply, map_pow]
    congr 1
    have hVi : V i * U i = 1 := congrFun hVU i
    have h1 := congrArg (W.γ₀ δ) hVi
    rw [map_mul, hUΔ δ hδ i, map_one] at h1
    exact mul_right_cancel₀ (hUu i).ne_zero (h1.trans hVi.symm)
  · have hγÊ : W.γA W.gam Ê = Ê * U := funext fun i => hUeq i
    rw [hK, map_pow, hγÊ]
    calc V ^ h' * (Ê * U) ^ h' = (V * U) ^ h' * Ê ^ h' := by ring
      _ = Ê ^ h' := by rw [hVU, one_pow, one_mul]

end U2C

end Formalism.MainNotions.N.Ln34
end
end
