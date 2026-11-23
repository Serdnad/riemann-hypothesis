module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import ReciprocityTheory.GroupCohomology.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.FinGen
import ReciprocityTheory.GroupCohomology.IsSuccSubset
public import ReciprocityTheory.GroupCohomology.Bundle004
public import ReciprocityTheory.GroupCohomology.Bundle005
public import ReciprocityTheory.GroupCohomology.Bundle006

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
open ReciprocityTheory.Coh
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

private noncomputable def redT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    TRep ℤ_[l] G :=
  { V := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) (m + 1)
    ccs := ⟨fun _ => continuous_of_discreteTopology⟩
    rho := redRep ρ (m + 1)
    cont := contAction_redRep h (m + 1) }

private instance redT_disc (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    DiscreteTopology (redT ρ h m).V := discrete_quot_lSub l n (m + 1)

private instance redT_fin (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Finite (redT ρ h m).V := finite_quot_lSub l n (m + 1)

private theorem lSub_le {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    lSub l X (m + 1) ≤ (lSub l X m).comap LinearMap.id := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_lSub.mp hx
  show (l : ℤ_[l]) ^ (m + 1) • y ∈ lSub l X m
  exact mem_lSub.mpr ⟨(l : ℤ_[l]) • y, by rw [pow_succ, mul_smul]⟩

private noncomputable def tauL (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    (X ⧸ lSub l X (m + 1)) →ₗ[ℤ_[l]] (X ⧸ lSub l X m) :=
  Submodule.mapQ _ _ LinearMap.id (lSub_le m)

private theorem tauL_mk {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) (x : X) :
    tauL l X m (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem tauL_equiv {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (ρ : Representation ℤ_[l] G X) (m : ℕ)
    (g : G) (y : X ⧸ lSub l X (m + 1)) : tauL l X m (redRep ρ (m + 1) g y) = redRep ρ m g (tauL l X m y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [redRep_mk, tauL_mk, tauL_mk, redRep_mk]

private theorem tauL_surj {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    Function.Surjective (tauL l X m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private noncomputable def tauT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair (redT ρ h (m + 1)) (redT ρ h m) :=
  Pair.ofMap (M := redT ρ h (m + 1)) (M' := redT ρ h m)
    (tauL l (Fin n → ℤ_[l]) (m + 1)) continuous_of_discreteTopology (tauL_equiv ρ (m + 1))

private noncomputable def piT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G) (redT ρ h m) :=
  Pair.ofMap (M := ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) (M' := redT ρ h m)
    (lSub l (Fin n → ℤ_[l]) (m + 1)).mkQ (continuous_mkQ _) (fun g x => (redRep_mk ρ (m + 1) g x).symm)

private theorem eq_zero_of_lSub (x : Fin n → ℤ_[l]) (hx : ∀ m, x ∈ lSub l (Fin n → ℤ_[l]) (m + 1)) : x = 0 := by
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [Pi.zero_apply, map_zero]
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    exact Subsingleton.elim _ _
  | succ k => exact mem_lSub_pi.mp (hx k) i

private theorem towerLim (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Cx.IsTowerLim (fun m => (redT ρ h m).coch) (fun m => (tauT ρ h m).hom)
      (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) fun m => (piT ρ h m).hom := by
  refine limRep_holds ℤ_[l] G (fun m => redT ρ h m) (tauT ρ h) _ (piT ρ h)
    (fun m => ⟨rfl, rfl, tauL_surj (m + 1), fun x => rfl⟩) ?_ ?_
  · have hc : Continuous fun (x : Fin n → ℤ_[l]) (m : ℕ) => (piT ρ h m).u x :=
      continuous_pi fun m => (piT ρ h m).u_cont
    refine (hc.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_lSub
    intro m
    have := congr_fun hxy m
    exact (Submodule.Quotient.eq _).mp this
  · intro y hy
    let S : ℕ → Set (Fin n → ℤ_[l]) := fun m => (piT ρ h m).u ⁻¹' {y m}
    have hS : (⋂ m, S m).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      · intro m x hx
        show (piT ρ h m).u x = y m
        have hx' : (piT ρ h (m + 1)).u x = y (m + 1) := hx
        rw [← hy m, ← hx']
        rfl
      · intro m
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y m)
        exact ⟨x, hx⟩
      · exact isCompact_univ.of_isClosed_subset
          ((isClosed_singleton).preimage (piT ρ h 0).u_cont) (Set.subset_univ _)
      · intro m
        exact (isClosed_singleton).preimage (piT ρ h m).u_cont
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, fun m => Set.mem_iInter.mp hx m⟩

private theorem smul_emb (m : ℕ) : IsEmbedding fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ m • x := by
  have hc : (l : ℤ_[l]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine (Continuous.isClosedEmbedding (continuous_const_smul _) ?_).isEmbedding
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

private theorem finH {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) (M : TRep ℤ_[l] G) [Finite M.V]
    [DiscreteTopology M.V] : (∀ k, Finite (M.H k)) ∧ ∀ k, 2 < k → Subsingleton (M.H k) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hF M.V M.rho M.cont
  obtain ⟨hN, ⟨e0, -⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := low_holds ℤ_[l] G M
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · match k with
    | 0 => exact Finite.of_equiv _ e0.symm.toEquiv
    | 1 => exact Finite.of_equiv _ e1.symm.toEquiv
    | 2 => exact Finite.of_equiv _ e2.symm.toEquiv
    | k + 3 =>
      obtain ⟨e, -⟩ := hN (k + 3)
      haveI := h3 (k + 3) (by omega)
      exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨e, -⟩ := hN k
    haveI := h3 k (by omega)
    exact e.toEquiv.subsingleton

end

theorem UpperTheory.latticeCochains_finGen_of_finLevel :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ}, FinLevel l G χ d → ∀ {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 := by
  intro l _ G _ _ _ χ d hF n ρ h
  haveI : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ inferInstance
  have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hT := towerLim ρ h
  have htors : ∀ (k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      (l : ℤ_[l]) • x = 0 → x = 0 := by
    intro k x hx
    apply Subtype.ext
    funext g
    have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k =>
      z.1 g) hx
    exact (smul_eq_zero.mp this).resolve_left hl
  have hker : ∀ (m k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      ((piT ρ h m).hom.f k) x = 0 ↔ ∃ y, x = (l : ℤ_[l]) ^ (m + 1) • y := by
    intro m k x
    have key : ((piT ρ h m).hom.f k) x = 0 ↔
        ∀ g, x.1 g ∈ lSub l (Fin n → ℤ_[l]) (m + 1) := by
      constructor
      · intro hx g
        have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch (redT ρ h m)).X k =>
          z.1 g) hx
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      · intro hx
        apply Subtype.ext
        funext g
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hx g)
    rw [key]
    constructor
    · intro hx
      choose y hy using fun g => mem_lSub.mp (hx g)
      have hyc : Continuous y := by
        apply (smul_emb (n := n) (l := l) (m + 1)).continuous_iff.mpr
        have : (fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ (m + 1) • x) ∘ y =
            x.1 := funext hy
        rw [this]
        exact x.2
      refine ⟨⟨y, hyc⟩, ?_⟩
      apply Subtype.ext
      funext g
      exact (hy g).symm
    · rintro ⟨y, rfl⟩ g
      exact mem_lSub.mpr ⟨y.1 g, rfl⟩
  have hfin : ∀ m, (∀ k, Finite ((redT ρ h m).H k)) ∧ ∀ k, 2 < k → Subsingleton ((redT ρ h m).H k) :=
    fun m => finH hF (redT ρ h m)
  have hlen0 : ∀ k, IsFiniteLength ℤ_[l] ((redT ρ h 0).coch.H k) := fun k => by
    haveI := (hfin 0).1 k
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have res := ReciprocityTheory.Coh.finGen_holds ℤ_[l] (l : ℤ_[l]) _ _ _ _ hT htors hker hlen0
  refine ⟨fun k => (res k).1, fun k hk => ?_⟩
  have ext := (ReciprocityTheory.Coh.tower_holds ℤ_[l] _ _ _ _ hT k).2 (fun j _ m => by
    haveI := (hfin m).1 j
    infer_instance)
  refine ⟨fun a b => ?_⟩
  have ha := ext a (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  have hb := ext b (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  rw [ha, hb]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

open ReciprocityTheory.Coh in
private theorem latGrow_bound {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ)
    (hF : Cx.FinGen (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) 2) (k : ℕ) :
    ∃ C : ℕ, ∀ m : ℕ,
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat ≤
        m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) + C ∧
      m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) ≤
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat := by
  let L : TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρ, cont := h }
  refine ⟨(length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H k))).toNat +
    (length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H (k + 1)))).toNat, fun m => ?_⟩
  let C : TRep ℤ_[l] G := { V := _, rho := redRep ρ m, cont := contAction_redRep h m }
  have hc : Continuous (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) :=
    continuous_const_smul ((l : ℤ_[l]) ^ m)
  let i : Pair L L := Pair.ofMap (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) hc
    fun g x => (map_smul (ρ g) ((l : ℤ_[l]) ^ m) x).symm
  let p : Pair L C := Pair.ofMap (lSub l (Fin n → ℤ_[l]) m).mkQ (continuous_mkQ _) fun _ _ => rfl
  have hl : (l : ℤ_[l]) ^ m ≠ 0 := pow_ne_zero _ PadicInt.irreducible_p.ne_zero
  have hA : admitted i p := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · refine (hc.isClosedEmbedding ?_).isEmbedding
      exact smul_right_injective (Fin n → ℤ_[l]) hl
    · exact LinearMap.exact_map_mkQ_range _
    · exact ⟨Function.surjInv (lSub l (Fin n → ℤ_[l]) m).mkQ_surjective,
        continuous_of_discreteTopology (α := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m),
        Function.surjInv_eq _⟩
  have hR := (rankLen_holds ℤ_[l] (l : ℤ_[l]) PadicInt.irreducible_p L.coch C.coch i.hom p.hom m 2
    (fun _ _ => rfl) (admissibility_holds _ _ _ _ _ i p hA) hF).2.2 k
  exact ⟨hR.1.trans (add_assoc _ _ _).le, hR.2⟩

private theorem latGrow_card {l : ℕ} [Fact l.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[l] M]
    [AddCommGroup N] [Module ℤ_[l] N] [Finite N] (e : M ≃ₗ[ℤ_[l]] N) {a b : ℕ}
    (h : (length ℤ_[l] M).toNat ≤ b ∧ a ≤ (length ℤ_[l] M).toNat) :
    l ^ a ≤ Nat.card N ∧ Nat.card N ≤ l ^ b := by
  obtain ⟨k, hk, hc⟩ := UpperTheory.V.Kum.lenOfCard l N
  rw [e.length_eq, hk, ENat.toNat_coe] at h
  rw [hc]
  have hp : 0 < l := (Fact.out : l.Prime).pos
  exact ⟨Nat.pow_le_pow_right hp h.2, Nat.pow_le_pow_right hp h.1⟩

open ReciprocityTheory.Coh in
theorem UpperTheory.lattice_cohomology_finite_and_growth_of_finGen :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 → (∀ m, Finite (H1 (redRep ρ m)) ∧ Finite (H2 (redRep ρ m))) → Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧ Grows l (fun m => Nat.card ↥(H0 (redRep ρ m))) (finrank ℤ_[l] ↥(H0 ρ)) ∧ Grows l (fun m => Nat.card (H1 (redRep ρ m))) (finrank ℤ_[l] (H1 ρ)) ∧ Grows l (fun m => Nat.card (H2 (redRep ρ m))) (finrank ℤ_[l] (H2 ρ)) := by
  intro l _ G _ _ _ n ρ h hF hfin
  obtain ⟨-, ⟨e₀, -⟩, ⟨e₁, -⟩, e₂, -⟩ :=
    low_holds ℤ_[l] G ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)
  have hq := fun m => low_holds ℤ_[l] G ({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G)
  haveI := hF.1 1
  haveI := hF.1 2
  refine ⟨Module.Finite.equiv e₁, Module.Finite.equiv e₂, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 0
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, ⟨q, -⟩, -⟩ := hq m
    rw [e₀.finrank_eq] at hC
    haveI : Finite (H0 (redRep ρ m)) := inferInstance
    exact latGrow_card (N := H0 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 1
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, ⟨q, -⟩, -⟩ := hq m
    rw [e₁.finrank_eq] at hC
    haveI := (hfin m).1
    exact latGrow_card (N := H1 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 2
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, -, q, -⟩ := hq m
    rw [e₂.finrank_eq] at hC
    haveI := (hfin m).2
    exact latGrow_card (N := H2 (redRep ρ m)) q (hC m)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

section SlopeTestRemainingChoices
open MvPowerSeries

private theorem low_mem {R σ : Type} [CommRing R] [Finite σ] (m : Ideal (MvPowerSeries σ R))
    (hF : ∀ s, (MvPowerSeries.X s : MvPowerSeries σ R) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : truncTotal n g = 0) : g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.fg_idealOfVars σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    rw [hg]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem mem_max {E σ : Type} [Field E] (a : MvPowerSeries σ E) :
    a ∈ maximalIdeal _ ↔ MvPowerSeries.constantCoeff a = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem mem_sq {E σ : Type} [Field E] [Finite σ] (g : MvPowerSeries σ E)
    (h0 : MvPowerSeries.constantCoeff g = 0) (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) g = 0) :
    g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2 := by
  refine low_mem _ (fun s => (mem_max _).2 (by simp)) 2 g ?_
  ext d
  rw [coeff_truncTotal_eq_ite]
  split_ifs with hd
  · have : d.degree = 0 ∨ d.degree = 1 := by omega
    rcases this with h | h
    · rw [Finsupp.degree_eq_zero_iff] at h
      subst h
      simpa using h0
    · obtain ⟨i, rfl⟩ : ∃ i, Finsupp.single i 1 = d := by
        have : d ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
          rw [Finsupp.range_single_one]; exact h
        exact this
      simpa using h1 i
  · simp

private theorem of_mem_sq {E σ : Type} [Field E] (g : MvPowerSeries σ E)
    (h : g ∈ maximalIdeal (MvPowerSeries σ E) ^ 2) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) g = 0 := by
  rw [pow_two] at h
  refine Submodule.mul_induction_on h (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_single_mul, (mem_max _).1 ha, (mem_max _).1 hb]; simp
  · rw [map_add (f := _), ha, hb, add_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (P : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → ∀ T : Submodule E (R →ₗ[O] E), (∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧ ∀ a ∈ P, δ a = 0) → Module.finrank E ↥T = n := by
  intro O R E _ _ _ _ _ _ _ n P x φ H T hT
  classical
  have hinj : Function.Injective (algebraMap O E) := IsFractionRing.injective O E
  have hne : ∀ c : O, c ≠ 0 → algebraMap O E c ≠ 0 := fun c hc h => hc (hinj (by simpa using h))
  let D : Fin n → (R →ₗ[O] E) := fun i =>
    ((MvPowerSeries.coeff (Finsupp.single i 1) : MvPowerSeries (Fin n) E →ₗ[E] E).restrictScalars O).comp
      φ.toLinearMap
  have hD : ∀ i a, D i a = MvPowerSeries.coeff (Finsupp.single i 1) (φ a) := fun i a => rfl
  have hDT : ∀ i, D i ∈ T := fun i => (hT _).2 ⟨fun a b => by
      rw [hD, hD, hD, map_mul, coeff_single_mul, H.const, H.const], fun a ha => by
      rw [← H.ker, RingHom.mem_ker] at ha
      rw [hD, ha, map_zero]⟩

  have hex : ∀ i : Fin n, ∃ (a : R) (c : O), c ≠ 0 ∧ ∀ j, D j a = if j = i then algebraMap O E c else 0 := by
    intro i
    obtain ⟨a, c, hc, h⟩ := H.dense 2 (MvPowerSeries.X i)
    refine ⟨a, c, hc, fun j => ?_⟩
    have := of_mem_sq _ h j
    rw [map_sub, sub_eq_zero, ← hD, ← algebraMap_smul E c, map_smul, MvPowerSeries.coeff_X] at this
    rw [← this]
    simp [Finsupp.single_left_inj]
  choose a c hc ha using hex
  have h1 : ∀ δ ∈ T, δ 1 = 0 := fun δ hδ => by
    have := ((hT δ).1 hδ).1 1 1
    simpa using this
  have hker : ∀ δ ∈ T, ∀ r, (∀ i, D i r = 0) → δ r = 0 := by
    intro δ hδ r hr
    have hsub : ∀ δ ∈ T, δ (r - x r • 1) = δ r := fun δ hδ => by
      rw [map_sub, map_smul, h1 δ hδ, smul_zero, sub_zero]
    have hm : φ (r - x r • 1) ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2 := by
      refine mem_sq _ ?_ fun i => ?_
      · rw [H.const]; simp
      · rw [← hD, hsub _ (hDT i), hr]
    obtain ⟨k, hk, hmem⟩ := H.inj 2 _ hm
    have hz : ∀ s ∈ RingHom.ker x ^ 2 ⊔ P, δ s = 0 := by
      intro s hs
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hs
      rw [map_add (f := _), ((hT δ).1 hδ).2 v hv, add_zero]
      rw [pow_two] at hu
      refine Submodule.mul_induction_on hu (fun p hp q hq => ?_) (fun p q hp hq => ?_)
      · rw [RingHom.mem_ker] at hp hq
        rw [((hT δ).1 hδ).1, hp, hq]; simp
      · rw [map_add (f := _), hp, hq, add_zero]
    have := hz _ hmem
    rw [map_smul, hsub δ hδ, Algebra.smul_def] at this
    exact (mul_eq_zero.1 this).resolve_left (hne k hk)
  let ev : T →ₗ[E] (Fin n → E) := LinearMap.pi fun i => (LinearMap.applyₗ' E (a i)).comp T.subtype
  have hev : ∀ (δ : T) i, ev δ i = (δ : R →ₗ[O] E) (a i) := fun _ _ => rfl
  have hbij : Function.Bijective ev := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro δ hδ
      ext r
      obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
        (fun i => D i r / algebraMap O E (c i))
      choose! b hb using hk
      have hz := hker δ δ.2 ((k : O) • r - ∑ i, b i • a i) (fun j => by

        rw [map_sub, map_sum, map_smul]
        simp only [map_smul, ha, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Algebra.smul_def, Algebra.smul_def, hb j (Finset.mem_univ _), Algebra.smul_def]
        have := hne _ (hc j)
        field_simp
        ring)

      rw [map_sub, map_sum, map_smul] at hz
      simp only [map_smul, ← hev, hδ, Pi.zero_apply, smul_zero, Finset.sum_const_zero, sub_zero] at hz
      rw [Algebra.smul_def] at hz
      exact (mul_eq_zero.1 hz).resolve_left (hne k (nonZeroDivisors.coe_ne_zero k))
    · intro v
      refine ⟨∑ j, (v j / algebraMap O E (c j)) • ⟨D j, hDT j⟩, ?_⟩
      ext i

      rw [map_sum, Finset.sum_apply]
      simp only [hev, Submodule.coe_smul, LinearMap.smul_apply, ha, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [smul_eq_mul, div_mul_cancel₀ _ (hne _ (hc i))]
  rw [(LinearEquiv.ofBijective ev hbij).finrank_eq]
  simp
end
