module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle366
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrix
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle368
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
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.Burnside

theorem span_top_of_residue {G O n : Type} [CommRing O] [IsLocalRing O] [Fintype n] [DecidableEq n] (T : G → Matrix n n O)
    (h : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (T g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range T) = ⊤ := by
  have hB : ∀ B : Matrix n n (IsLocalRing.ResidueField O), ∃ M ∈ Submodule.span O (Set.range T),
      M.map (IsLocalRing.residue O) = B := fun B => by
    have hM : B ∈ Submodule.span (IsLocalRing.ResidueField O)
        (Set.range fun g => (T g).map (IsLocalRing.residue O)) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact ⟨T g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Matrix.map_zero _ (map_zero _)⟩
    | add B B' _ _ h h' =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨M', hM', rfl⟩ := h'
      exact ⟨M + M', Submodule.add_mem _ hM hM', Matrix.map_add _ (map_add _) _ _⟩
    | smul t B _ h =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      exact ⟨t • M, Submodule.smul_mem _ _ hM, by ext p q; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson _) fun M _ => ?_
  obtain ⟨M', hM', e⟩ := hB (M.map (IsLocalRing.residue O))
  have e1 : M = M' + (M - M') := by abel
  rw [e1]
  refine Submodule.add_mem_sup hM' ?_
  rw [Matrix.matrix_eq_sum_single (M - M')]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have e2 : Matrix.single p q ((M - M') p q) = (M - M') p q • Matrix.single p q (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e2]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun e p) q).symm

theorem eq_top_of_map {G O A n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
    (T : G → Matrix n n O) (h : Submodule.span O (Set.range T) = ⊤) (S : Submodule A (Matrix n n A))
    (hS : ∀ g, (T g).map (algebraMap O A) ∈ S) : S = ⊤ := by
  have hB : ∀ B : Matrix n n O, B.map (algebraMap O A) ∈ S := fun B => by
    have hM : B ∈ Submodule.span O (Set.range T) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact hS g
    | zero => rw [Matrix.map_zero _ (map_zero _)]; exact Submodule.zero_mem _
    | add B B' _ _ h h' => rw [Matrix.map_add _ (map_add _)]; exact Submodule.add_mem _ h h'
    | smul t B _ h =>
      have : (t • B).map (algebraMap O A) = algebraMap O A t • B.map (algebraMap O A) := by ext p q; simp
      rw [this]
      exact Submodule.smul_mem _ _ h
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have : Matrix.single p q (M p q) = M p q • (Matrix.single p q (1 : O)).map (algebraMap O A) := by
    rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (hB _)

theorem span_twist_eq_top : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Submodule.span A (Set.range fun g => ((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) = ⊤ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS
  refine eq_top_of_map (fun g => ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)))
    (span_top_of_residue _ hS.1.2.1.1) _ fun g => ?_
  have : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A) =
      (algebraMap (X.O0 i) A ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) * (((κ g)⁻¹ : Aˣ) : A)) •
        (((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) := by
    rw [smul_smul, Units.inv_mul_cancel_right]
    ext p q
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← map_mul, Units.mul_inv_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end GlobalTheory.NewPrime.Burnside
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.pointGaloisReps_conjugate_over_fraction_field : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  first | exact @GlobalTheory.PointRepConj.main | exact GlobalTheory.PointRepConj.main | (intros; apply GlobalTheory.PointRepConj.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.selmer_theorem_of_local_components : KernelRep → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → SelMaps bkP i s κ Q ∧ SelLeft bkP i s κ Q ∧ SelColim bkP i s κ Q ∧ SelObs bkP i s κ Q) → ThmS bkP := by
  first | exact @GlobalTheory.SelAssemble.thmS_of_selmer_functor | exact GlobalTheory.SelAssemble.thmS_of_selmer_functor | (intros; apply GlobalTheory.SelAssemble.thmS_of_selmer_functor <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

theorem _root_.GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix : KernelRep := by
  first | exact @GlobalTheory.KRep.kernelRep | exact GlobalTheory.KRep.kernelRep | (intros; apply GlobalTheory.KRep.kernelRep <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ClassRefine

open scoped Classical

variable {G : Type*} [Group G] (Q : Subgroup G)

def stabQ (J : Subgroup G) (t : G) : Subgroup Q :=
  (J.comap (MulAut.conj t⁻¹).toMonoidHom).comap Q.subtype

variable {Q}

theorem mem_stabQ {J : Subgroup G} {t : G} {q : Q} : q ∈ stabQ Q J t ↔ t⁻¹ * (q : G) * t ∈ J := by
  rw [stabQ, Subgroup.mem_comap, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_subtype]

theorem card_stabQ_eq (J : Subgroup G) (t : G) :
    Nat.card (stabQ Q J t) = Nat.card {q : Q // t⁻¹ * (q : G) * t ∈ J} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_stabQ)

theorem card_stabQ_left (J : Subgroup G) (x : G) (γ : Q) :
    Nat.card (stabQ Q J ((γ : G) * x)) = Nat.card (stabQ Q J x) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨γ⁻¹ * q * γ, ?_⟩
      invFun := fun q => ⟨γ * q * γ⁻¹, ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · have := mem_stabQ.1 q.2
    rw [mem_stabQ]; simpa [mul_assoc] using this
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  · exact Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem card_stabQ_split {J J' : Subgroup G} (hJ : J' ≤ J) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J)
    (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') (t s : G) (γ₀ : Q) (κ₀ : G) (hκ₀ : κ₀ ∈ J)
    (hs : s = (γ₀ : G) * t * κ₀) :
    Nat.card (stabQ Q J t) =
      (F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j).card * Nat.card (stabQ Q J' s) := by
  have hex : ∀ κ ∈ J, ∃ u, u ∈ F ∧ u⁻¹ * κ ∈ J' := fun κ hκ => (hFu κ hκ).exists
  choose! uF huF hJu using hex
  have huniq : ∀ κ ∈ J, ∀ u ∈ F, u⁻¹ * κ ∈ J' → u = uF κ := fun κ hκ u hu h =>
    (hFu κ hκ).unique ⟨hu, h⟩ ⟨huF κ hκ, hJu κ hκ⟩
  have hSΓ : stabQ Q J' (t * κ₀) ≤ stabQ Q J t := by
    intro q hq
    rw [mem_stabQ] at hq ⊢
    have : κ₀ * ((t * κ₀)⁻¹ * (q : G) * (t * κ₀)) * κ₀⁻¹ ∈ J :=
      J.mul_mem (J.mul_mem hκ₀ (hJ hq)) (J.inv_mem hκ₀)
    simpa [mul_assoc] using this
  set Γ := stabQ Q J t with hΓ
  set S := stabQ Q J' (t * κ₀) with hS
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t * u = q * s * j with hU
  let κf : Γ → G := fun q => t⁻¹ * ((q : Q) : G) * t * κ₀
  have hκ : ∀ q : Γ, κf q ∈ J := fun q => J.mul_mem (mem_stabQ.1 q.2) hκ₀
  have hψ : ∀ q : Γ, uF (κf q) ∈ U := by
    intro q
    rw [hU, Finset.mem_filter]
    refine ⟨huF _ (hκ q), (q : Q) * γ₀⁻¹, ((uF (κf q))⁻¹ * κf q)⁻¹, J'.inv_mem (hJu _ (hκ q)), ?_⟩
    simp only [κf, hs]
    push_cast
    group
  let ψ : Γ → U := fun q => ⟨uF (κf q), hψ q⟩
  have hresp : ∀ a b : Γ, a⁻¹ * b ∈ S.subgroupOf Γ → ψ a = ψ b := by
    intro a b h
    rw [Subgroup.mem_subgroupOf, hS, mem_stabQ] at h
    apply Subtype.ext
    show uF (κf a) = uF (κf b)
    refine huniq (κf b) (hκ b) (uF (κf a)) (huF _ (hκ a)) ?_
    have e : (uF (κf a))⁻¹ * κf b =
        ((uF (κf a))⁻¹ * κf a) * ((t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀)) := by
      simp only [κf]
      push_cast
      group
    rw [e]
    exact J'.mul_mem (hJu _ (hκ a)) h
  let Φ : Γ ⧸ S.subgroupOf Γ → U := Quotient.lift ψ (fun a b h => hresp a b (QuotientGroup.leftRel_apply.1 h))
  have hΦ : ∀ a : Γ, Φ (a : Γ ⧸ S.subgroupOf Γ) = ψ a := fun a => rfl
  have hbij : Function.Bijective Φ := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hΦ, hΦ] at hxy
      have hab : uF (κf a) = uF (κf b) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hS, mem_stabQ]
      have h1 := hJu _ (hκ a)
      have h2 := hJu _ (hκ b)
      rw [hab] at h1
      have e : (t * κ₀)⁻¹ * (((a⁻¹ * b : Γ) : Q) : G) * (t * κ₀) =
          ((uF (κf b))⁻¹ * κf a)⁻¹ * ((uF (κf b))⁻¹ * κf b) := by
        simp only [κf]
        push_cast
        group
      rw [e]
      exact J'.mul_mem (J'.inv_mem h1) h2
    · rintro ⟨u, hu⟩
      have hu' := hu
      rw [hU, Finset.mem_filter] at hu'
      obtain ⟨huF', q, j, hj, e⟩ := hu'
      have hu_eq : u = t⁻¹ * ((q : G) * ((γ₀ : G) * t * κ₀) * j) := by
        rw [← hs, ← e]; group
      have hmem : t⁻¹ * (((q * γ₀ : Q)) : G) * t = u * j⁻¹ * κ₀⁻¹ := by
        rw [hu_eq]; push_cast; group
      have hqΓ : q * γ₀ ∈ Γ := by
        rw [hΓ, mem_stabQ, hmem]
        exact J.mul_mem (J.mul_mem (hF u huF') (J.inv_mem (hJ hj))) (J.inv_mem hκ₀)
      refine ⟨((⟨q * γ₀, hqΓ⟩ : Γ) : Γ ⧸ S.subgroupOf Γ), ?_⟩
      rw [hΦ]
      apply Subtype.ext
      show uF (κf ⟨q * γ₀, hqΓ⟩) = u
      refine (huniq _ (hκ _) u huF' ?_).symm
      have e2 : u⁻¹ * κf ⟨q * γ₀, hqΓ⟩ = j⁻¹ := by
        show u⁻¹ * (t⁻¹ * (((q * γ₀ : Q)) : G) * t * κ₀) = j⁻¹
        rw [hmem]; group
      rw [e2]
      exact J'.inv_mem hj
  have h1 := Subgroup.card_mul_index (S.subgroupOf Γ)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSΓ).toEquiv, Subgroup.index,
    Nat.card_eq_of_bijective Φ hbij, Nat.card_eq_finsetCard] at h1
  have h2 : Nat.card (stabQ Q J' s) = Nat.card S := by
    rw [hS, hs, mul_assoc]
    exact card_stabQ_left J' (t * κ₀) γ₀
  rw [h2, ← h1, mul_comm]

theorem sum_classReps_refine {J J' : Subgroup G} (hJ : J' ≤ J) {T T' : Finset G}
    (hT : ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Q) (κ : G), κ ∈ J ∧ g = (γ : G) * t * κ)
    (hT' : ∀ g : G, ∃! t, t ∈ T' ∧ ∃ (γ : Q) (κ : G), κ ∈ J' ∧ g = (γ : G) * t * κ)
    (φ : G → ℂ) (hφQ : ∀ (γ : Q) g, φ ((γ : G) * g) = φ g) (hφJ : ∀ κ ∈ J', ∀ g, φ (g * κ) = φ g)
    {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ J) (hFu : ∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') :
    ∑ t' ∈ T', ((Nat.card (stabQ Q J' t') : ℂ))⁻¹ * φ t' =
      ∑ t ∈ T, ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * ∑ u ∈ F, φ (t * u) := by
  choose! rep hrepT hrep using fun g => (hT' g).exists
  have hrepeq : ∀ g t', t' ∈ T' → ∀ (γ : Q) (κ : G), κ ∈ J' → g = γ * t' * κ → rep g = t' :=
    fun g t' ht' γ κ hκ e => (hT' g).unique ⟨hrepT g, hrep g⟩ ⟨ht', γ, κ, hκ, e⟩
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product' (f := fun t u => ((Nat.card (stabQ Q J t) : ℂ))⁻¹ * φ (t * u)),
    ← Finset.sum_fiberwise_of_maps_to (s := T ×ˢ F) (t := T') (g := fun p => rep (p.1 * p.2))
      (fun p _ => hrepT _)]
  refine Finset.sum_congr rfl fun t' ht' => ?_
  obtain ⟨t₀, ht₀, γ₀, κ₀, hκ₀, e₀⟩ := (hT t').exists
  set U := F.filter fun u => ∃ (q : Q) (j : G), j ∈ J' ∧ t₀ * u = q * t' * j with hU
  have hfib : (T ×ˢ F).filter (fun p => rep (p.1 * p.2) = t') = {t₀} ×ˢ U := by
    ext ⟨a, u⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, hU]
    constructor
    · rintro ⟨⟨ha, hu⟩, hp⟩
      obtain ⟨γ, κ, hκ, e⟩ := hrep (a * u)
      rw [hp] at e
      have ha0 : a = t₀ := by
        refine (hT a).unique ⟨ha, 1, 1, J.one_mem, by simp⟩
          ⟨ht₀, γ * γ₀, κ₀ * κ * u⁻¹, J.mul_mem (J.mul_mem hκ₀ (hJ hκ)) (J.inv_mem (hF u hu)), ?_⟩
        have ea : a = a * u * u⁻¹ := by group
        rw [ea, e, e₀]
        push_cast
        group
      subst ha0
      exact ⟨rfl, hu, γ, κ, hκ, e⟩
    · rintro ⟨rfl, hu, q, j, hj, e⟩
      exact ⟨⟨ht₀, hu⟩, hrepeq _ t' ht' q j hj e⟩
  rw [hfib, Finset.sum_product, Finset.sum_singleton]
  have hval : ∀ u ∈ U, ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ (t₀ * u) =
      ((Nat.card (stabQ Q J t₀) : ℂ))⁻¹ * φ t' := by
    intro u hu
    rw [hU, Finset.mem_filter] at hu
    obtain ⟨_, q, j, hj, e⟩ := hu
    rw [e, mul_assoc, hφQ, hφJ j hj]
  rw [Finset.sum_congr rfl hval, Finset.sum_const,
    card_stabQ_split hJ hF hFu t₀ t' γ₀ κ₀ hκ₀ e₀]
  have hne : U.card ≠ 0 := by
    obtain ⟨u, hu, hj⟩ := (hFu κ₀ hκ₀).exists
    refine Finset.card_ne_zero_of_mem (s := U) (a := u) ?_
    rw [hU, Finset.mem_filter]
    refine ⟨hu, γ₀⁻¹, (u⁻¹ * κ₀)⁻¹, J'.inv_mem hj, ?_⟩
    rw [e₀]
    push_cast
    group
  have hc : (U.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  rw [nsmul_eq_mul, Nat.cast_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem classSum_smaller_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), IsInvForm a β → ∀ (J J' : Subgroup (GAf L n)) (T T' : Finset (GAf L n)), IsBounded J → J' ≤ J → J'.relIndex J ≠ 0 → IsClassReps J T → IsClassReps J' T' → ∀ f ∈ NG.AFall L n a.ρ, ∀ f' ∈ NG.AFall L n a.ρ, (∀ κ ∈ J', ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g)) → ∀ F : Finset (GAf L n), (∀ κ ∈ F, κ ∈ J) → (∀ κ ∈ J, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ J') → classSum a β J' T' f f' = ∑ t ∈ T, ((Nat.card {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} : ℕ) : ℂ)⁻¹ * ∑ u ∈ F, β (f (t * u)) (f' (t * u)) := by
  intro L _ _ _ n a β hβ J J' T T' _ hJ _ hT hT' f hf f' hf' hinv F hF hFu
  have key := sum_classReps_refine (Q := GQ L n) hJ hT hT' (fun g => β (f g) (f' g))
    (fun γ g => by rw [hf.1 γ g, hf'.1 γ g, hβ.2.2]) (fun κ hκ g => hinv κ hκ g) hF hFu
  simp only [card_stabQ_eq] at key
  exact key

end GlobalTheory.ClassRefine

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.PointEigen

theorem genAt_iff_splitOut (D : D7) (i : D.nd.Loc) (v : PlE D.host) (k : ℕ) :
    GenAt D (D.nd.l i) (D.nd.Q i) v k ↔ (SplitOut D.nd i v ∧ 1 ≤ k ∧ k ≤ D.R.nV) := by
  have hS : v ∈ D.nd.S i ↔ v ∈ placesS D (D.nd.l i) := by
    rw [D.nd.S_def]; rfl
  unfold SplitOut GenAt
  rw [hS]
  tauto

theorem ptSys_mem_eigSet : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ (i : D.nd.Loc) (x : D.nd.X i),
    ptSys D i x ∈ EigSet (M.loc i) (D.nd.l i) (D.nd.Q i) := by
  intro D M A i x
  refine ⟨fun v k h => ?_, ?_⟩
  · simp only [ptSys, if_neg h]
  · obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (D.naut.typeV_ne i P)
    refine ⟨y, hy0, fun v k s ϖ hg hc hu => ?_⟩
    obtain ⟨hw, k1, k2⟩ := (genAt_iff_splitOut D i v k).1 hg
    simp only [ptSys, if_pos hg]
    exact (A.ptV i P x).1 hP v k s ϖ hw hc hu k1 k2 y hy

end GlobalTheory.PointEigen
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ZDecompAt

theorem zDecomp_of_cheb : GlobalTheory.TwSys.Cheb → ∀ (D : D7), GlobalTheory.BlockComplement.GaloisRepsCusp D →
    ∀ i : D.nd.Loc, ZDecomp D.nd i := by
  intro hC D hG i π hπ r hr
  obtain ⟨ρ, hρ⟩ := GlobalTheory.BlockComplement.complement_at hC D hG i π hπ r hr
  obtain ⟨e, he⟩ := hρ.rho
  exact ⟨ρ, e, fun g u => he g u⟩

end GlobalTheory.ZDecompAt
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EigFinite

theorem eigSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  intro hP D μ j X l Q B hB hBv
  classical
  have hex := GlobalTheory.SplitConjPlace.splitEx_all D
  let ι := {p : PlE D.host × ℕ // GenAt D l Q p.1 p.2}
  have hch : ∀ i : ι, ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host i.1.1 s.w ∧ IsUnif D.host.E s.v ϖ := fun i => hex i.1.1 i.2.1
  choose s ϖ hs hϖ using hch
  have hfact := fun i : ι => hP D.host.E D.R.nV X.wt X.J X.χ B X.J_open hB (s i) (ϖ i) i.1.2
    (hBv _ _ _ i.2 (hs i)) (hϖ i) i.2.2.2.2.2.1 i.2.2.2.2.2.2
  have hTS : ∀ y, X.real y ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun y => X.real_range ▸ LinearMap.mem_range_self X.real y
  have hmem : ∀ (i : ι) (y : D.what₂.Mt μ j), ∃ y', X.real y' = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => by
    have h := (hfact i).1 _ (hTS y)
    rw [← X.real_range] at h
    exact h
  choose g hg using hmem
  have h0 : ∀ i : ι, NG.tN X.J (s i) (ϖ i) i.1.2 0 = 0 := fun i => by
    have h := (hfact i).2.1 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at h
    simpa using h
  let op : ι → Module.End ℂ (D.what₂.Mt μ j) := fun i =>
    { toFun := g i
      map_add' := fun y y' => X.real_inj (by
        rw [hg, map_add (f := _), map_add (f := _), hg, hg]
        have h := (hfact i).2.1 _ (hTS y) _ (hTS y') 1
        simpa using h)
      map_smul' := fun c y => X.real_inj (by
        rw [hg, map_smul, map_smul, hg]
        have h := (hfact i).2.1 _ (hTS y) 0 (Submodule.zero_mem _) c
        simpa [h0] using h) }
  have hop : ∀ i y, X.real (op i y) = NG.tN X.J (s i) (ϖ i) i.1.2 (X.real y) := fun i y => hg i y
  have hcomm : ∀ i i' : ι, Commute (op i) (op i') := fun i i' => by
    ext y
    apply X.real_inj
    show X.real (op i (op i' y)) = X.real (op i' (op i y))
    rw [hop, hop, hop, hop]
    exact (hfact i).2.2.1 (s i') (ϖ i') i'.1.2 (hBv _ _ _ i'.2 (hs i')) (hϖ i') i'.2.2.2.2.2.1 i'.2.2.2.2.2.2 _ (hTS y)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo op
    (fun i i' φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm i' i) φ)
  have hfin : {χ : ι → ℂ | ⨅ i, (op i).maxGenEigenspace (χ i) ≠ ⊥}.Finite :=
    Set.finite_coe_iff.mp (@Finite.of_fintype _ hind.fintypeNeBotOfFiniteDimensional)
  let Φ : (PlE D.host → ℕ → ℂ) → (ι → ℂ) := fun c i => c i.1.1 i.1.2
  apply Set.Finite.of_finite_image (f := Φ)
  · apply hfin.subset
    rintro _ ⟨c, ⟨-, y, hy0, hy⟩, rfl⟩
    show ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) ≠ ⊥
    intro hbot
    apply hy0
    have hyin : y ∈ ⨅ i, (op i).maxGenEigenspace (c i.1.1 i.1.2) := by
      rw [Submodule.mem_iInf]
      intro i
      apply Module.End.eigenspace_le_maxGenEigenspace
      rw [Module.End.mem_eigenspace_iff]
      apply X.real_inj
      rw [hop, map_smul]
      exact hy i.1.1 i.1.2 (s i) (ϖ i) i.2 (hs i) (hϖ i)
    rw [hbot] at hyin
    exact (Submodule.mem_bot ℂ).1 hyin
  · rintro c ⟨hc, -⟩ c' ⟨hc', -⟩ hcc
    funext v k
    by_cases h : GenAt D l Q v k
    · exact congrFun hcc ⟨(v, k), h⟩
    · rw [hc v k h, hc' v k h]

end GlobalTheory.EigFinite
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.isBaseCond_of_split_primes : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ P : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ P.asIdeal → Splits (below P)) → PlacesOk H q0 w0 → IsBaseCond (cond0 H w0) := by
  first | exact @GlobalTheory.LamTie.isBaseCond_cond0 | exact GlobalTheory.LamTie.isBaseCond_cond0 | (intros; apply GlobalTheory.LamTie.isBaseCond_cond0 <;> assumption)
end
