module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle271
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle568
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle045
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle035
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelChoices

open Formalism.L2.Host Formalism.L2.Herm

variable {D : D7}

theorem mem_crdLat (V : HSp D) (x : Fin V.rank → D.host.E) : x ∈ crdLat V V.L0 ↔ (crd V).symm x ∈ V.L0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (crd V).symm (crd V y) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, (crd V).apply_symm_apply x⟩

theorem coe_crdLat (V : HSp D) : (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) = L0c D V := by
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  show V.frame.equivFun.symm x ∈ V.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem dualL_crdLat (V : HSp D) : dualL D.sp.cm V (crdLat V V.L0) = crdLat V V.L0 := by
  unfold dualL
  conv_rhs => rw [← Submodule.span_eq (crdLat V V.L0)]
  congr 1
  ext x
  rw [SetLike.mem_coe, mem_crdLat]
  conv_rhs => rw [← V.baseLattice_isUnimodular]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  constructor
  · intro h y hy
    have := h (crd V y) ⟨y, hy, rfl⟩
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply]
    exact this
  · rintro h _ ⟨y, hy, rfl⟩
    have := h y hy
    rw [hT_crd D.sp.cm, LinearEquiv.apply_symm_apply] at this
    exact this

theorem isSDFrame_of_one {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) (N : ℕ) : IsSDFrame V β Λ N := by
  obtain ⟨c, hc⟩ := h
  refine ⟨0, ?_⟩
  rw [one_pow] at hc
  rwa [pow_zero]

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) :
    χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem exists_levCh (D : D7) (C : CharFrame D) (T : Type) (μ0 : T) (ξ : T → HChar D.host.E)
    (Q : T → Finset (Pl D.host.E)) (hinj : Function.Injective ξ) (hbase : ξ μ0 = 1)
    (hfin : ∀ t, ∃ n : ℕ, 0 < n ∧ (ξ t).OrderDvd n) (htriv : ∀ t, (ξ t).TrivOn D.host.F)
    (htame : ∀ t v, (ξ t).TameAt v) (hpl : ∀ t, Lev.IsTwistPlaces D.host.g (Q t))
    (hoff : ∀ t, ∀ PP ∈ Q t, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
      ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (hde : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
      ∀ t, ∀ PP ∈ Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭)
    (hram : ∀ t PP, ¬ (ξ t).UnrAt PP ↔ PP ∈ Q t ∨ ∃ PP' ∈ Q t, Lev.IsConjPl PP' PP) :
    ∃ L : LevCh D T, L.C = C ∧ L.xiH = ξ ∧ L.Q = Q ∧ (∀ j, L.ΛY j = crdLat _ (Yc D j).L0) ∧ L.Is μ0 := by
  classical
  choose m hm using fun j : Fin D.R.m => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (C.mu0 j) (C.isMu0 j).unitary
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D C.eta C.isEta.unitary
  choose x hx using fun t => GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar D (ξ t) (by obtain ⟨n, hn, h⟩ := hfin t; exact isUnitary_of_orderDvd hn h)
  choose r hr using fun (j : Fin D.R.m) PP => GlobalTheory.exists_isRes_of_tameAt D (C.mu0 j) PP ((C.isMu0 j).tame PP)
  choose s hs using fun t PP => GlobalTheory.exists_isRes_of_tameAt D (ξ t) PP (htame t PP)
  choose β hβ using fun V : HSp D => GlobalTheory.T.exists_selfDual_adelic_frame_level_one D V (crdLat V V.L0) (coe_crdLat V) (dualL_crdLat V)
  refine ⟨{ C := C, xiH := ξ
            mu0 := fun j => if h : j - 1 < D.R.m then m ⟨j - 1, h⟩ else 1
            eta := η, xi := x
            Pg := Finset.univ.biUnion fun k => aboveF (L := D.host.E) D.host.K (C.P.pb k)
            Q := Q
            chi := fun j PP => if h : j - 1 < D.R.m then (r ⟨j - 1, h⟩ PP)⁻¹ else 1
            xiR := s
            ΛY := fun _ => crdLat _ (HSpace.L0 _), ΛX := crdLat _ (HSpace.L0 _)
            ΛV := fun _ => crdLat _ (HSpace.L0 _), ΛW := fun _ => crdLat _ (HSpace.L0 _)
            βY := fun _ => β _, βX := β _, βV := fun _ => β _, βW := fun _ => β _ }, rfl, rfl, rfl, fun _ => rfl, ?_⟩
  exact
    { mu0 := fun j => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h]
        exact hm j
      eta := hη, xi := hx, xi_inj := hinj, xi_base := hbase, xi_fin := hfin, xi_triv := htriv, xi_tame := htame
      Pg := fun PP => by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, aboveF, Set.Finite.mem_toFinset]
        rfl
      Q_pl := hpl, Q_off := hoff, Q_de := hde, Q_ram := hram
      chi := fun j PP _ => by
        have h : (j : ℕ) + 1 - 1 < D.R.m := j.2
        simp only [dif_pos h, inv_inv]
        exact hr j PP
      xiR := fun t PP _ => hs t PP
      βY := fun j _ => isSDFrame_of_one (hβ _) _
      βX := hβ _, βV := fun _ => hβ _, βW := fun _ => hβ _ }

theorem exists_levCh_unit : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D), ∃ L : LevCh D Unit, L.C = C ∧ L.Is () := by
  intro D C
  obtain ⟨L, h1, -, -, -, h2⟩ := exists_levCh D C Unit () (fun _ => 1) (fun _ => ∅) (fun _ _ _ => rfl) rfl
    (fun _ => ⟨1, one_pos, one_pow 1⟩) (fun _ => (isPsi_one (H := D.host) 2).triv) (fun _ _ _ _ _ => rfl)
    (fun _ _ h => absurd h (Finset.notMem_empty _)) (fun _ _ h => absurd h (Finset.notMem_empty _))
    (fun _ _ => ⟨C.P.pb 0, fun _ _ h => absurd h (Finset.notMem_empty _)⟩)
    (fun _ _ => iff_of_false (fun h => h fun _ _ => rfl) (by simp))
  exact ⟨L, h1, h2⟩

end GlobalTheory.LevelChoices
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem isClosed_singleton_of_isAdic {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (c : O) :
    IsClosed ({c} : Set O) := by
  have e : ({c} : Set O) = ⋂ M : ℕ, (fun x => x - c) ⁻¹'
      ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro rfl M
      simp
    · intro h
      have h2 := Ideal.mem_iInf.2 h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
      simpa [sub_eq_zero] using h2
  rw [e]
  refine isClosed_iInter fun M => IsClosed.preimage (continuous_id.sub continuous_const) ?_
  exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ M : Ideal O).toAddSubgroup
    ((isAdic_iff.1 had).1 M)

theorem joint_pow_of_tameGen : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  intro E Ω _ _ _ _ _ A γ hγ O _ _ _ _ _ had χ hχ m hm0 hm hI e π hπ he
  set q : Ω := γ π / π with hqdef
  have hroot : ∀ τ : G E Ω, (τ π / π) ^ m = 1 := by
    intro τ
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hq : q ^ m = 1 := hroot γ
  have hc : χ γ ^ m = 1 := hI γ hγ.1
  have hinv : ∀ {M : Type} [Group M] (x : M), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro M _ x hx n
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_add, show n * (m - 1) + n = n * m by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [Nat.mul_add]]
    rw [pow_mul', hx, one_pow]
  have hinv0 : ∀ (x : Ω), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro x hx n
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0.ne'] at hx
      exact zero_ne_one hx
    have := hinv (Units.mk0 x hx0) (by ext; simpa using hx) n
    have := congrArg (fun u : Ωˣ => (u : Ω)) this
    simpa using this
  let H : Subgroup (G E Ω) :=
    { carrier := {σ | σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = q ^ n}
      mul_mem' := by
        rintro σ τ ⟨hσ, n₁, h₁, h₁'⟩ ⟨hτ, n₂, h₂, h₂'⟩
        refine ⟨mul_mem hσ hτ, n₁ + n₂, ?_, ?_⟩
        · rw [map_mul, h₁, h₂, pow_add]
        · rw [quot_mul hσ m hm hπ he, h₁', h₂', pow_add]
      one_mem' := ⟨one_mem _, 0, by simp, by simp [div_self hπ]⟩
      inv_mem' := by
        rintro σ ⟨hσ, n, h₁, h₁'⟩
        have hσi : σ⁻¹ ∈ Ine (F := E) A := inv_mem hσ
        refine ⟨hσi, n * (m - 1), ?_, ?_⟩
        · rw [map_inv, h₁, hinv _ hc]
        · have h3 := quot_mul hσi m hm hπ he (τ := σ)
          rw [inv_mul_cancel, AlgEquiv.one_apply, div_self hπ, h₁'] at h3
          rw [← hinv0 q hq, eq_inv_of_mul_eq_one_left h3.symm] }
  have hclosed : IsClosed (H : Set (G E Ω)) := by
    have e : (H : Set (G E Ω)) = (Ine (F := E) A : Set (G E Ω)) ∩
        ⋃ n ∈ Finset.range m, ({σ : G E Ω | ((χ σ : Oˣ) : O) = ((χ γ ^ n : Oˣ) : O)} ∩
          {σ : G E Ω | σ π = q ^ n * π}) := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hσ, n, h₁, h₁'⟩
        refine ⟨hσ, n % m, Nat.mod_lt _ hm0, ?_, ?_⟩
        · rw [h₁, ← pow_mod_orderOf, ← pow_mod_orderOf (χ γ) (n % m)]
          congr 2
          have hd := orderOf_dvd_of_pow_eq_one hc
          rw [Nat.mod_mod_of_dvd _ hd]
        · rw [← pow_mod_orderOf, ← div_eq_iff hπ, h₁']
          rw [← pow_mod_orderOf q n]
          congr 1
          rw [Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hq)]
      · rintro ⟨hσ, n, -, h₁, h₁'⟩
        exact ⟨hσ, n, Units.ext h₁, by rw [h₁', mul_div_cancel_right₀ _ hπ]⟩
    rw [e]
    refine (isClosed_Ine A).inter (isClosed_biUnion_finset fun n _ => IsClosed.inter ?_ ?_)
    · exact (isClosed_singleton_of_isAdic had _).preimage hχ
    · exact isClosed_setOf_apply π (fun y => y = q ^ n * π)
  intro σ hσ
  have hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro τ (rfl | hτ)
    · exact ⟨hγ.1, 1, by simp, by simp [hqdef]⟩
    · have hτI : τ ∈ Ine (F := E) A := GlobalTheory.TameGenPowers.wild_mem_Ine hτ
      refine ⟨hτI, 0, ?_, ?_⟩
      · rw [pow_zero]
        exact GlobalTheory.WildSetSQ.char_eq_one_of_wild A had χ hχ τ hτ m hm (hI τ hτI)
      · rw [pow_zero]
        exact eq_one_of_pow_eq_one A hm (hroot τ) (hτ π hπ)
  have hmem := closure_minimal (SetLike.coe_subset_coe.2 hle) hclosed (hγ.2 hσ)
  exact hmem.2

end GlobalTheory.TameTau
end

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.Unfold

theorem tsum_indicator_coset_complex {G : Type} [Group G] (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ℂ) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := isTopologicalGroup_of_discreteTopology
  have h := congrArg ENNReal.toReal (GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin x)
  rw [ENNReal.tsum_toReal_eq (fun γ => by
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ]; simp)] at h
  have h2 := congrArg (fun r : ℝ => (r : ℂ)) h
  simp only [Complex.ofReal_tsum] at h2
  convert h2 using 1
  · congr 1; funext γ
    by_cases hγ : γ • x ∈ (fun y => a⁻¹ * y) ⁻¹' (K : Set G)
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]; simp
    · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem hγ]; simp
  · by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem unfold_coset (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G)
    [Countable Γ] (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (f : G → ℂ)
    (hfl : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hf : IntegrableOn f ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) ν) :
    IntegrableOn f {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} (ν.restrict 𝓖) ∧
    ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ℂ) *
      ∫ x in {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}, f x ∂(ν.restrict 𝓖)
      = ∫ x in (fun y => a⁻¹ * y) ⁻¹' (K : Set G), f x ∂ν := by
  set A := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hAdef
  set C := {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} with hCdef
  set n := {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard with hndef
  have hA : MeasurableSet A := (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hC : MeasurableSet C := (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hn : n ≠ 0 := ((Set.ncard_pos hfin).2 ⟨1, Γ.one_mem, by simp⟩).ne'
  have hcount : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ENNReal) (γ • x) = (n : ENNReal) * C.indicator 1 x :=
    GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin
  have hcountC : ∀ x, ∑' γ : Γ, A.indicator (1 : G → ℂ) (γ • x) = (n : ℂ) * C.indicator 1 x :=
    tsum_indicator_coset_complex Γ K a hfin
  have hφ : Integrable (A.indicator f) ν := hf.integrable_indicator hA
  have hpt : ∀ (γ : Γ) x, A.indicator f (γ • x) = A.indicator (1 : G → ℂ) (γ • x) * f x := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hptE : ∀ (γ : Γ) x,
      ‖A.indicator f (γ • x)‖ₑ = A.indicator (1 : G → ENNReal) (γ • x) * ‖f x‖ₑ := by
    intro γ x
    have : f (γ • x) = f x := hfl γ γ.2 x
    by_cases hx : γ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, one_mul, this]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, eNorm_zero]
  have hmeasγ : ∀ γ : Γ, AEStronglyMeasurable (fun x => A.indicator f (γ • x)) (ν.restrict 𝓖) := by
    intro γ
    exact (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_smul γ ν).quasiMeasurePreserving).restrict
  have hlin : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν = ∫⁻ x, ‖A.indicator f x‖ₑ ∂ν :=
    (h𝓖.lintegral_eq_tsum'' (fun x => ‖A.indicator f x‖ₑ)).symm
  have hlin2 : ∑' γ : Γ, ∫⁻ x in 𝓖, ‖A.indicator f (γ • x)‖ₑ ∂ν
      = (n : ENNReal) * ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) := by
    rw [← lintegral_tsum (fun γ => (hmeasγ γ).eNorm)]
    simp_rw [hptE, ENNReal.tsum_mul_right, hcount]
    rw [← lintegral_indicator hC, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ C
    · simp [Set.indicator_of_mem hx, hndef]
    · simp [Set.indicator_of_notMem hx]
  have hCU : C = ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' A := by
    ext x
    simp only [hCdef, hAdef, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      have : a⁻¹ * (γ⁻¹ * (γ * a * k)) = k := by group
      simpa [this] using hk
    · rintro ⟨γ, hγ⟩
      exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hγ, by group⟩
  have hintγ : ∀ γ : Γ, IntegrableOn f ((fun x => (γ : G) * x) ⁻¹' A) ν := by
    intro γ
    have := ((measurePreserving_mul_left ν (γ : G)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (γ : G)) (f := f) (s := A)).2 hf
    have hfeq : f ∘ (fun x => (γ : G) * x) = f := funext fun x => hfl γ γ.2 x
    rwa [hfeq] at this
  have hmeasC : AEStronglyMeasurable f ((ν.restrict 𝓖).restrict C) := by
    have : AEStronglyMeasurable f (ν.restrict C) := by
      rw [hCU, aestronglyMeasurable_iUnion_iff]
      exact fun γ => (hintγ γ).aestronglyMeasurable
    exact this.mono_measure (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
  have hfinC : ∫⁻ x in C, ‖f x‖ₑ ∂(ν.restrict 𝓖) ≠ ⊤ := by
    intro htop
    have h1 := hlin2.symm.trans hlin
    rw [htop, ENNReal.mul_top (by exact_mod_cast hn)] at h1
    exact hφ.hasFiniteIntegral.ne h1.symm
  have hintC : IntegrableOn f C (ν.restrict 𝓖) := ⟨hmeasC, hfinC.lt_top⟩
  refine ⟨hintC, ?_⟩
  rw [← integral_indicator hA, h𝓖.integral_eq_tsum'' _ hφ,
    ← integral_tsum hmeasγ (by rw [hlin]; exact hφ.hasFiniteIntegral.ne)]
  simp_rw [hpt, tsum_mul_right, hcountC]
  rw [← integral_indicator hC, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ C
  · simp [Set.indicator_of_mem hx, hndef]
  · simp [Set.indicator_of_notMem hx]

end GlobalTheory.Unfold

namespace GlobalTheory.Unfold

theorem integral_fundamentalDomain_eq_sum_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  intro G _ _ _ _ _ ν _ Γ Ω _ 𝓖 h𝓖 hΩ ι _ h huniq hfin f hfl hf
  set C : ι → Set G := fun i => {x : G | ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k} with hCdef
  have hC : ∀ i, MeasurableSet (C i) := fun i =>
    (GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ Ω hΩ (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simp⟩).ne'
  have hpre : ∀ i, (fun y => h i * y) ⁻¹' ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) = Ω := by
    intro i; ext k; simp
  have hA : ∀ i, IntegrableOn f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G)) ν := by
    intro i
    refine ((measurePreserving_mul_left ν (h i)).integrableOn_comp_preimage
      (measurableEmbedding_mulLeft (h i))).1 ?_
    rw [hpre]; exact hf i
  have hAint : ∀ i, ∫ x in (fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G), f x ∂ν
      = ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
    intro i
    have := (measurePreserving_mul_left ν (h i)).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft (h i)) f ((fun y => (h i)⁻¹ * y) ⁻¹' (Ω : Set G))
    rw [hpre] at this
    exact this.symm
  have hU := fun i => unfold_coset ν Γ Ω 𝓖 h𝓖 hΩ (h i) (hfin i) f hfl (hA i)
  have hF : f = fun x => ∑ i, (C i).indicator f x := by
    funext x
    obtain ⟨i, hi, hu⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ C i from hi)]
    · intro j _ hj
      exact Set.indicator_of_notMem (s := C j) (fun hx => hj (hu j hx)) f
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hint : ∀ i, Integrable ((C i).indicator f) (ν.restrict 𝓖) := fun i =>
    (integrable_indicator_iff (hC i)).2 (hU i).1
  refine ⟨?_, ?_⟩
  · rw [IntegrableOn, hF]
    exact integrable_finsetSum _ fun i _ => hint i
  · have h1 : ∫ x in 𝓖, f x ∂ν = ∫ x in 𝓖, ∑ i, (C i).indicator f x ∂ν := by
      conv_lhs => rw [hF]
    rw [h1, integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator (hC i), ← hAint i, ← (hU i).2]
    have : (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos i
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

end GlobalTheory.Unfold
end
