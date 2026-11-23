module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle444
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle446
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle445
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.DualClass

section Algebra

noncomputable def chr {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n) (y' : B') :
    AddChar B ℂ := (ZMod.stdAddChar (N := n)).compAddMonoidHom (P.flip y')

theorem chr_injective {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] (P : B →+ B' →+ ZMod n)
    (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Function.Injective (chr P) := by
  intro u v huv
  refine sub_eq_zero.1 (h _ fun y => ?_)
  rw [map_sub, sub_eq_zero]
  exact ZMod.injective_stdAddChar (DFunLike.congr_fun huv y)

theorem card_addChar (B : Type) [AddCommGroup B] [Finite B] : Nat.card (AddChar B ℂ) = Nat.card B := by
  classical
  have := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card (α := AddChar B ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

theorem card_le_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) : Nat.card B' ≤ Nat.card B := by
  rw [← card_addChar B]
  exact Nat.card_le_card_of_injective _ (chr_injective P h)

theorem left_of_right {n : ℕ} [NeZero n] {B B' : Type} [AddCommGroup B] [AddCommGroup B'] [Finite B]
    (P : B →+ B' →+ ZMod n) (h : ∀ y', (∀ y, P y y' = 0) → y' = 0) (hc : Nat.card B ≤ Nat.card B') (y : B)
    (hy : ∀ y', P y y' = 0) : y = 0 := by
  have hb := (chr_injective P h).bijective_of_nat_card_le (by rw [card_addChar]; exact hc)
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  obtain ⟨y', rfl⟩ := hb.2 ψ
  change ZMod.stdAddChar (P y y') = 1
  rw [hy, AddChar.map_zero_eq_one]

variable {A : Type} [CommRing A]

theorem card_ker_eq_coker {M : Type} [AddCommGroup M] [Module A M] [Finite M] (f : M →ₗ[A] M) :
    Nat.card (LinearMap.ker f) = Nat.card (M ⧸ LinearMap.range f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h3 : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right h3 ?_
  rw [← h1, mul_comm, ← h2]

abbrev Quo (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Type := Y ⧸ LinearMap.range (LinearMap.lsmul A Y c)

abbrev Tor (c : A) (Y : Type) [AddCommGroup Y] [Module A Y] : Submodule A Y := LinearMap.ker (LinearMap.lsmul A Y c)

variable {n : ℕ} {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y']

theorem exists_induced (β : Y →+ Y' →+ ZMod n) (hβ : Bal A β) (c : A) :
    ∃ β₂ : Quo c Y →+ Tor c Y' →+ ZMod n, ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1 := by
  let P : Y →+ Tor c Y' →+ ZMod n := (β.flip.comp (Tor c Y').subtype.toAddMonoidHom).flip
  refine ⟨QuotientAddGroup.lift (LinearMap.range (LinearMap.lsmul A Y c)).toAddSubgroup P ?_, fun y y' => rfl⟩
  rintro _ ⟨y, rfl⟩
  refine AddMonoidHom.mem_ker.2 (AddMonoidHom.ext fun y' => ?_)
  change β (c • y) y'.1 = 0
  have h : c • y'.1 = 0 := y'.2
  rw [hβ, h, map_zero]

theorem perf_induced [NeZero n] [Finite Y] [Finite Y'] (β : Y →+ Y' →+ ZMod n) (hβ : Perf A β) (c : A)
    (β₂ : Quo c Y →+ Tor c Y' →+ ZMod n) (h : ∀ y y', β₂ (Submodule.Quotient.mk y) y' = β y y'.1) : Perf A β₂ := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have : Finite (Quo c Y') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hr : ∀ y', (∀ y, β₂ y y' = 0) → y' = 0 := fun y' hy =>
    Subtype.ext (hβ.2.2 _ fun y => by rw [← h, hy])
  refine ⟨fun a y y' => ?_, left_of_right β₂ hr ?_, hr⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, h, h, hβ.1]
    rfl
  · obtain ⟨γ, hγ⟩ := exists_induced (A := A) β.flip (fun a y' y => (hβ.1 a y y').symm) c
    rw [← card_ker_eq_coker, card_ker_eq_coker (LinearMap.lsmul A Y' c)]
    exact card_le_of_right γ fun y hy => Subtype.ext (hβ.2.1 _ fun y' => by
      have := hy (Submodule.Quotient.mk y')
      rwa [hγ] at this)

theorem smul_mem_range [Finite Y] {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : Nat.card (LinearMap.ker (matAct (M := Y) Φ)) ≤ Nat.card (LinearMap.ker (matAct (M := Quo c Y) Φ)))
    (w : Fin a → Y) : c • w ∈ LinearMap.range (matAct (M := Y) Φ) := by
  have : Finite (Quo c Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [card_ker_eq_coker, card_ker_eq_coker] at h
  let f : (Fin a → Y) →ₗ[A] (Fin a → Quo c Y) := (Submodule.mkQ _).compLeft (Fin a)
  have hf : LinearMap.range (matAct (M := Y) Φ) ≤ (LinearMap.range (matAct (M := Quo c Y) Φ)).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, funext fun b => ?_⟩

    simp [f, matAct, map_sum]
  have hs : Function.Surjective (Submodule.mapQ _ _ f hf) := by
    intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    choose u hu using fun b => Submodule.Quotient.mk_surjective _ (x b)
    exact ⟨Submodule.Quotient.mk u, by rw [Submodule.mapQ_apply]; exact congrArg _ (funext hu)⟩
  have : Finite ((Fin a → Y) ⧸ LinearMap.range (matAct (M := Y) Φ)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have hb := hs.bijective_of_nat_card_le h
  rw [← Submodule.Quotient.mk_eq_zero]
  apply hb.1
  rw [map_zero, Submodule.mapQ_apply]
  have h0 : f (c • w) = 0 := funext fun b => (Submodule.Quotient.mk_eq_zero _).2 ⟨w b, rfl⟩
  rw [h0, Submodule.Quotient.mk_zero]

theorem mul_eq_zero_of_range (β : Y →+ A →+ ZMod n) (hβ : Perf A β) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (c : A)
    (h : ∀ w : Fin a → Y, c • w ∈ LinearMap.range (matAct (M := Y) Φ)) (y₀ : Fin a → A) (h0 : Matrix.vecMul y₀ Φ = 0)
    (j : Fin a) : c * y₀ j = 0 := by
  refine hβ.2.2 _ fun w => ?_
  obtain ⟨x, hx⟩ := h (Pi.single j w)
  have h1 : ∑ b, y₀ b • matAct Φ x b = 0 := by
    change ∑ b, y₀ b • ∑ k, Φ b k • x k = 0
    simp only [Finset.smul_sum, ← mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h2 : ∑ b, y₀ b * Φ b k = 0 := congrFun h0 k
    rw [← Finset.sum_smul, h2, zero_smul]
  rw [hx, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  have h3 : (c * y₀ j) • w = 0 := by
    rw [mul_comm, mul_smul]
    simpa using h1
  have h4 := hβ.1 (c * y₀ j) w 1
  rw [h3, smul_eq_mul, mul_one] at h4
  rw [← h4]
  simp

end Algebra

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i) {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host))

theorem card_selOn {a : ℕ} (Φ : Matrix (Fin a) (Fin a) A) (Z : GE N → Matrix (Fin D.R.r) (Fin a) A)
    (h : Univ bkP i s κ Q Φ Z) (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] :
    Nat.card (LinearMap.ker (matAct (M := Y) Φ)) = Nat.card (selOn bkP i (Tgl i s) κ Y Q) := by
  obtain ⟨h1, h2, h3⟩ := h Y
  choose z hz hz' using fun x : LinearMap.ker (matAct (M := Y) Φ) => h1 x.1 x.2
  refine Nat.card_eq_of_bijective (fun x => ⟨_, hz' x⟩) ⟨fun x x' hx => ?_, fun q => ?_⟩
  · have e := (Submodule.Quotient.eq _).1 (congrArg Subtype.val hx)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 e
    refine sub_eq_zero.1 (Subtype.ext (h2 _ (x - x').2 ⟨m, fun g => ?_⟩))
    rw [← hm g]
    change _ = (z x).1 g - (z x').1 g
    rw [hz, hz]
    funext b
    simp [rect, smul_sub]
  · obtain ⟨q, hq⟩ := q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, m, hm⟩ := h3 y.1 ⟨y, rfl, hq⟩
    refine ⟨⟨x, hx⟩, Subtype.ext (Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)))⟩
    rw [← hm g]
    change y.1 g - (z ⟨x, hx⟩).1 g = _
    rw [hz]


omit [Algebra (X.O0 i) A] in
theorem card_invariants_torsion_submodule {Γ O : Type} [Group Γ] [CommRing O] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ)
    (U : Subgroup Γ) (Y' : Type) [AddCommGroup Y'] [Module A Y'] (c : A)
    (h : ∀ m, (∀ g ∈ U, repOn ρ κ Y' g m = m) → c • m = 0) :
    Nat.card (H0 ((repOn ρ κ (Tor c Y')).comp U.subtype)) = Nat.card (H0 ((repOn ρ κ Y').comp U.subtype)) := by
  refine Nat.card_eq_of_bijective (fun m => ⟨(Tor c Y').subtype.compLeft (Fin r) m.1, fun g => ?_⟩)
    ⟨fun m m' hm => ?_, fun m => ?_⟩
  · exact (repOn_map ρ κ (Tor c Y').subtype g.1 m.1).symm.trans (congrArg _ (m.2 g))
  · exact Subtype.ext (funext fun b => Subtype.ext (congrFun (congrArg Subtype.val hm) b))
  · have h0 := h m.1 fun g hg => m.2 ⟨g, hg⟩
    refine ⟨⟨fun b => ⟨m.1 b, congrFun h0 b⟩, fun g => funext fun b => Subtype.ext ?_⟩, rfl⟩
    exact (congrFun (repOn_map ρ κ (Tor c Y').subtype g.1 _) b).trans (congrFun (m.2 g) b)

theorem exists_not_cob : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → NoInvDual i κ ρ → OrderFormula bkP i s κ ρ Q → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] (β : Y →+ A →+ ZMod (X.l i ^ (nu X i + 1))), Perf A β → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (c t : A) (y₀ : Fin a → A) (j : Fin a), (∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ A g m = m) → t • m = 0) → Matrix.vecMul y₀ Φ = 0 → c * t * y₀ j ≠ 0 → ∃ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y ∧ ¬ Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) := by
  intro D N X bkP i s A _ _ _ _ _ _ κ Q ρ hS hK hD hN hO Y _ _ _ _ _ β hβ a Φ Z hU c t y₀ j ht h0 hne
  by_contra hcon
  have hcob : ∀ y : Z1 (repOn ρ κ⁻¹ A), DualSel bkP i s κ ρ β Q y → Cob (repOn ρ κ⁻¹ A) (fun g => c • y.1 g) :=
    fun y hy => by_contra fun h => hcon ⟨y, hy, h⟩
  haveI : NeZero (X.l i ^ (nu X i + 1)) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  letI : TopologicalSpace (Quo (c * t) Y) := ⊥
  haveI : DiscreteTopology (Quo (c * t) Y) := ⟨rfl⟩
  haveI : Finite (Quo (c * t) Y) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  obtain ⟨β₂, hβ₂⟩ := exists_induced β hβ.1 (c * t)
  have hP := perf_induced β hβ (c * t) β₂ hβ₂
  obtain ⟨-, e1⟩ := hO Y A β hβ
  obtain ⟨f2, e2⟩ := hO (Quo (c * t) Y) (Tor (c * t) A) β₂ hP
  have hsub : DualCl bkP i s κ ρ β Q ⊆ h1Map ρ κ⁻¹ (Tor (c * t) A).subtype '' DualCl bkP i s κ ρ β₂ Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y₂, hy₂, m, hm⟩ := GlobalTheory.T.dualSelmerClass_from_coeffsKilledBy_mul D N X bkP i s A κ Q ρ hS hK hD hN Y A (Quo (c * t) Y) (Tor (c * t) A) β β₂
      (Submodule.mkQ _) (Tor (c * t) A).subtype c t hβ.1 hP.1 (Submodule.mkQ_surjective _) (Submodule.injective_subtype _)
      (fun y' h => ⟨⟨y', h⟩, rfl⟩) hβ₂ ht y hy (hcob y hy)
    exact ⟨_, ⟨y₂, hy₂, rfl⟩, Eq.symm ((Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m, hm⟩))⟩
  have hfin : (DualCl bkP i s κ ρ β₂ Q).Finite := f2
  have hle : Nat.card (DualCl bkP i s κ ρ β Q) ≤ Nat.card (DualCl bkP i s κ ρ β₂ Q) :=
    (Set.ncard_le_ncard hsub (hfin.image _)).trans (Set.ncard_image_le hfin)
  have hprod : ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ (Tor (c * t) A)).comp (DecV N v).subtype)) =
      ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ A).comp (DecV N v).subtype)) :=
    Finset.prod_congr rfl fun v hv => card_invariants_torsion_submodule ρ κ⁻¹ (DecV N v) A (c * t) fun m hm => by
      rw [mul_smul, ht v (Or.inr hv) m hm, smul_zero]
  refine hne (mul_eq_zero_of_range β hβ Φ (c * t) (smul_mem_range Φ (c * t) ?_) y₀ h0 j)
  rw [card_selOn bkP i s κ Q Φ Z hU, card_selOn bkP i s κ Q Φ Z hU, e1, e2, hprod]
  exact Nat.mul_le_mul_right _ hle

end GlobalTheory.NewPrime.DualClass
end

section

open ValuativeRel OnePoint GlobalTheory.LocGL.ProjLine

namespace GlobalTheory.LocGL.ProjLine

theorem exists_jump_point {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (f : k → ℂ) {r : k} (hr : r ≠ 0) (h : ∀ x, valuation k x ≤ valuation k r → f x = f 0) {y : k} (hy : f y ≠ f 0) :
    ∃ b : k, f b ≠ f 0 ∧ ∀ x, valuation k x < valuation k b → f x = f 0 := by
  classical
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hr' : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  have hex : ∃ n : ℕ, ∃ x, valuation k x * uniformizer k ^ n ≤ valuation k r ∧ f x ≠ f 0 := by
    have hy0 : 0 < valuation k y := zero_lt_iff.2 (by rintro h0; rw [map_eq_zero] at h0; exact hy (by rw [h0]))
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (uniformizer_lt_one (R := k))
      (Units.mk0 (valuation k r / valuation k y) (div_pos hr' hy0).ne')
    refine ⟨n, y, ?_, hy⟩
    rw [Units.val_mk0, lt_div_iff₀ hy0, mul_comm] at hn
    exact hn.le
  obtain ⟨b, hb, hb'⟩ := Nat.find_spec hex
  refine ⟨b, hb', fun x hx => ?_⟩
  by_contra hne
  rcases hm : Nat.find hex with _ | m
  · rw [hm, pow_zero, mul_one] at hb
    exact hb' (h b hb)
  · refine Nat.find_min hex (m := m) (by omega) ⟨x, ?_, hne⟩
    rw [hm] at hb
    have hb0 : 0 < valuation k b := zero_le'.trans_lt hx
    have h1 : valuation k x / valuation k b ≤ uniformizer k := le_uniformizer_iff.2 ((div_lt_one₀ hb0).2 hx)
    rw [div_le_iff₀ hb0] at h1
    calc valuation k x * uniformizer k ^ m ≤ uniformizer k * valuation k b * uniformizer k ^ m := by gcongr
      _ = valuation k b * uniformizer k ^ (m + 1) := by rw [pow_succ]; ac_rfl
      _ ≤ _ := hb

theorem ballFn_sub_mem_of_radial (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (S : Submodule ℂ (OnePoint k → ℂ)) (hS : Stable S) (F : OnePoint k → ℂ) (hF : F ∈ S)
    (hrad : ∀ u x : k, valuation k u = 1 → F ((u * x : k) : OnePoint k) = F (x : OnePoint k))
    (h0 : ∃ r : k, r ≠ 0 ∧ ∀ x : k, valuation k x ≤ valuation k r → F (x : OnePoint k) = F ((0 : k) : OnePoint k))
    (hi : ∃ R : k, ∀ x : k, valuation k R < valuation k x → F (x : OnePoint k) = F ∞)
    (hne : F ((0 : k) : OnePoint k) ≠ F ∞) (ϖ : k) (hϖ : valuation k ϖ = uniformizer k) :
    ballFn 0 ϖ - ballFn 1 ϖ ∈ S := by
  classical
  obtain ⟨r, hr, h0⟩ := h0
  obtain ⟨R, hi⟩ := hi
  have hπ : (0 : ValueGroupWithZero k) < uniformizer k := uniformizer_pos
  have hy : ∃ y : k, valuation k R < valuation k y := by
    by_cases hR : R = 0
    · exact ⟨1, by simp [hR]⟩
    · have hR' : 0 < valuation k R := zero_lt_iff.2 (by simpa using hR)
      refine ⟨R / ϖ, ?_⟩
      rw [map_div₀, hϖ, lt_div_iff₀ hπ]
      exact mul_lt_of_lt_one_right hR' uniformizer_lt_one
  obtain ⟨y, hy⟩ := hy
  obtain ⟨b, hb, hb'⟩ := exists_jump_point (fun x : k => F x) hr h0 (y := y) (by
    show F y ≠ F (0 : k)
    rw [hi y hy]; exact hne.symm)
  have hb0 : b ≠ 0 := by rintro rfl; exact hb rfl
  have hvb : 0 < valuation k b := zero_lt_iff.2 (by simpa using hb0)
  let g : k → ℂ := fun x => F ((b * x : k) : OnePoint k)
  have g1 : ∀ x, valuation k x < 1 → g x = F (0 : k) := fun x hx => hb' _ (by
    rw [map_mul]; exact mul_lt_of_lt_one_right hvb hx)
  have g2 : ∀ x, valuation k x = 1 → g x = F b := fun x hx => by
    show F ((b * x : k) : OnePoint k) = _
    rw [mul_comm]; exact hrad x b hx
  have g3 : ∀ x z, x ≠ 0 → valuation k z = valuation k x → g z = g x := fun x z hx hz => by
    have hvx : valuation k x ≠ 0 := by simpa using hx
    have := hrad (z / x) (b * x) (by rw [map_div₀, hz, div_self hvx])
    show F ((b * z : k) : OnePoint k) = F ((b * x : k) : OnePoint k)
    rw [← this]; congr 2; field_simp
  have hG : (fun x : OnePoint k => x.elim (F ∞) g) ∈ S :=
    hS.1 F hF b 0 hb0 _ rfl fun x => by rw [add_zero]; rfl
  have hG' : (fun x : OnePoint k => x.elim (F ∞) fun x => g (x - 1)) ∈ S :=
    hS.1 F hF b (-b) hb0 _ rfl fun x => by
      show F ((b * (x - 1) : k) : OnePoint k) = _
      congr 2; ring
  have hc : F (0 : k) - F b ≠ 0 := sub_ne_zero.2 hb.symm
  rw [← S.smul_mem_iff hc]
  convert S.sub_mem hG hG' using 1
  funext x
  induction x using OnePoint.rec with
  | infty => simp [ballFn]
  | coe x =>
    show (F (0 : k) - F b) * (ballFn 0 ϖ x - ballFn 1 ϖ x) = g x - g (x - 1)
    rw [ballFn_coe, ballFn_coe, hϖ, sub_zero]
    simp only [le_uniformizer_iff]
    by_cases h1 : valuation k x < 1
    · have h2 : valuation k (x - 1) = 1 := by
        rw [Valuation.map_sub_swap]; exact (valuation k).map_one_sub_of_lt h1
      rw [if_pos h1, if_neg (by rw [h2]; exact lt_irrefl _), g1 x h1, g2 _ h2]; ring
    · by_cases h2 : valuation k (x - 1) < 1
      · have h3 : valuation k x = 1 := by
          have := (valuation k).map_one_add_of_lt h2
          rwa [add_sub_cancel] at this
        rw [if_neg h1, if_pos h2, g1 _ h2, g2 _ h3]; ring
      · have hx0 : x ≠ 0 := by rintro rfl; exact h1 (by simp)
        have h3 : valuation k (x - 1) = valuation k x := by
          rcases (not_lt.1 h1).eq_or_lt with h4 | h4
          · refine le_antisymm ?_ (h4 ▸ not_lt.1 h2)
            exact (valuation k).map_sub_le le_rfl (by rw [map_one]; exact h4.le)
          · exact (valuation k).map_sub_eq_of_lt_left (by rwa [map_one])
        rw [if_neg h1, if_neg h2, g3 x _ hx0 h3]; ring

end GlobalTheory.LocGL.ProjLine
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem mul_rpow_self_le {x c C : ℝ} (hx : 1 ≤ x) (hc : c ≤ C) (hC : 0 ≤ C) :
    c * x ^ c ≤ C * x ^ C := by
  have h0 : 0 ≤ x ^ c := Real.rpow_nonneg (by linarith) _
  calc c * x ^ c ≤ C * x ^ c := mul_le_mul_of_nonneg_right hc h0
    _ ≤ C * x ^ C := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hc) hC

theorem admissible_parameters_design_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x)
    (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  intro eps Fm
  obtain ⟨C1, y1, h1⟩ := GlobalTheory.T.log_hostClassNumber_le_scale_pow_family Fm
  obtain ⟨C2, y2, h2⟩ := GlobalTheory.T.exists_log_card_restRows_le_pow_mul_length Fm
  set C : ℝ := max 1 (max (Fm.PK.getD 7 0) (max (Fm.PK.getD 19 0) (max (9 / 2 + 10 * eps + eps / 100)
    (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2)))))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC0 : 0 ≤ C := by linarith
  have hCLw : Fm.PK.getD 7 0 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCYL : Fm.PK.getD 19 0 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hrest : max (9 / 2 + 10 * eps + eps / 100)
      (max (2 + 8 * eps + eps / 100) (max (Fm.Ct + eps / 100) (max C1 C2))) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  have hK : 9 / 2 + 10 * eps + eps / 100 ≤ C := le_trans (le_max_left _ _) hrest
  have hN : 2 + 8 * eps + eps / 100 ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hrest
  have hT : Fm.Ct + eps / 100 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hc12 : max C1 C2 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hrest
  have hCC1 : C1 ≤ C := le_trans (le_max_left _ _) hc12
  have hCC2 : C2 ≤ C := le_trans (le_max_right _ _) hc12
  refine ⟨C, max y1 y2, hC1, fun x hxy hx i => ?_⟩
  have hx1 : 1 ≤ x := le_of_lt (lt_trans Fm.one_lt_family_threshold hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have heps : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hPK := Fm.params_K x hx i
  obtain ⟨sN, -, sK, -, sT, -, -, -, -, -, -, sDe2, -⟩ := Fm.sizes x hx i
  unfold SizeN szTh at sN
  unfold SizeK szTh at sK
  unfold SizeT szTh at sT
  unfold SizeDe2 at sDe2
  rw [hsx, heps] at sN sK
  rw [hsx, heps, Fm.Ct_eq x i] at sT
  have hmono : ∀ a : ℝ, a ≤ C → x ^ a ≤ x ^ C := fun a ha => Real.rpow_le_rpow_of_exponent_le hx1 ha
  have hLg : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (le_trans zero_le_one (le_of_lt (Fm.L x i).sc.one_lt_alt)) _
  unfold TwistedPlaces.ParametersPolynomiallyBounded
  refine ⟨?_, ?_, ?_, ?_, ?_, sDe2, ?_, ?_⟩
  · have e : (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by rw [← hPK]; rfl
    rw [e]; exact hCLw
  · have e : (Fm.params x hx i).CYL = Fm.PK.getD 19 0 := by rw [← hPK]; rfl
    rw [e]; exact hCYL
  · rw [hsx]; exact le_trans sK.2 (hmono _ hK)
  · rw [hsx]; exact le_trans sN.2 (hmono _ hN)
  · rw [hsx]; exact le_trans sT.2 (hmono _ hT)
  · rw [hsx]
    exact le_trans (h1 x (le_trans (le_max_left _ _) hxy) hx i) (mul_rpow_self_le hx1 hCC1 hC0)
  · rw [hsx]
    refine le_trans (h2 x (le_trans (le_max_right _ _) hxy) hx i) ?_
    exact mul_le_mul_of_nonneg_right (mul_rpow_self_le hx1 hCC2 hC0) hLg

end GlobalTheory.NLink
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) → ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  first | exact @GlobalTheory.TateEigen.finite_on_inertia | exact GlobalTheory.TateEigen.finite_on_inertia | (intros; apply GlobalTheory.TateEigen.finite_on_inertia <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.continuous_cochain_of_deRham_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (k : ℕ) (x : Fin k → V ⊗[ℚ_[l]] P.R.BdR) (β : Fin k → ↥(GK K) → ℚ_[l]), (∀ i, Continuous (β i)) → ∀ (x' : V ⊗[ℚ_[l]] P.R.BdR) (f : ↥(GK K) → V), (∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = ∑ i, β i g • x i + (actVdR (P.PD K) ρ g x' - x')) → Continuous f := by
  first | exact @GlobalTheory.ContDR.cont_dR | exact GlobalTheory.ContDR.cont_dR | (intros; apply GlobalTheory.ContDR.cont_dR <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  first | exact @GlobalTheory.NL.Expansion.levLaws | exact GlobalTheory.NL.Expansion.levLaws | (intros; apply GlobalTheory.NL.Expansion.levLaws <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial

namespace GlobalTheory.TypeAbove

theorem conj_over_split (D : D7) {p : ℕ} {w w' : PlE D.host} (hw : w ∈ placesOver D.host.E p)
    (hs : IsSplitPl D.host w) (hc : IsConjPl D.host w w') :
    w' ∈ placesOver D.host.E p ∧ IsSplitPl D.host w' := by
  have h := (GlobalTheory.ConjPlaceOff.isConjPl_iff D w w').1 hc
  refine ⟨?_, ?_⟩
  · have e := (h ((p : ℕ) : 𝓞 D.host.E)).1 hw
    rwa [map_natCast] at e
  · obtain ⟨x, hx, hcx⟩ := (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w).1 hs
    exact (GlobalTheory.ConjPlaceOff.isSplitPl_iff D w').2 ⟨_, (h x).1 hx, fun h' => hcx ((h _).2 h')⟩

end GlobalTheory.TypeAbove
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.wachEtaleModule_frobenius_basis : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ (r : ℕ) (b b' : Module.Basis (Fin r) W.EE (W.DD T)), ∀ j, b' j = W.φD T (b j) := by
  first | exact @GlobalTheory.EtaleFrob.phi_basis | exact GlobalTheory.EtaleFrob.phi_basis | (intros; apply GlobalTheory.EtaleFrob.phi_basis <;> assumption)
end
