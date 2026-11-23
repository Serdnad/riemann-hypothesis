module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle008
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open GlobalTheory.CuspRep.LocEx
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem fin_comm_loc (π : CuspSub E n) (w : Pl E) {c : GL (Fin n) (Af E)}
    (hc : GeneralLinearGroup.map (pLoc E w) c = 1) (g : GLw n w) (y : π.V) :
    π.finPart c (π.locRep w g y) = π.locRep w g (π.finPart c y) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, LocUniq.comm_locGL w hc]

private theorem null_cases (π : CuspSub E n) (w : Pl E) (K : Subgroup (GLw n w)) :
    nullPart (π.locRep w) K = ⊥ ∨ nullPart (π.locRep w) K = ⊤ := by
  have inj := Submodule.map_injective_of_injective π.V.injective_subtype
  have stable : ∀ o, ∀ x ∈ nullPart (π.locRep w) K, π.op o x ∈ nullPart (π.locRep w) K := by
    intro o x hx
    cases o with
    | fin k =>
      have e := map_pLoc_inv_mul w k
      have h1 := nullPart_act (π.locRep w) K (GeneralLinearGroup.map (pLoc E w) k)
        (nullPart_comm (π.locRep w) K (π.finPart ((locGL E n w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k))
          (fun g y => fin_comm_loc π w e g y) hx)
      rwa [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
    | cpt k =>
      refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
      change (rt E n (infGL E n (Unitary.toUnits k)) * rt E n (finGL E n (locGL E n w g))) y.1 =
        (rt E n (finGL E n (locGL E n w g)) * rt E n (infGL E n (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      exact nullPart_comm _ K _ (fun g y => Subtype.ext (LinearMap.congr_fun (lie_rt_fin X (locGL E n w g)) y.1)) hx
  refine (π.irred ((nullPart (π.locRep w) K).map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp
    (fun e => inj (e.trans (Submodule.map_bot _).symm)) fun e => inj (e.trans (Submodule.map_subtype_top _).symm)
  rintro o _ ⟨x, hx, rfl⟩
  exact ⟨_, stable o x hx, rfl⟩

private theorem step (π : CuspSub E n) (w : Pl E) (B : Multiset ℂˣ) (hB : HasSatGL w (π.locRep w) B)
    (U : Subgroup (GL (Fin n) (Af E))) (hU : ∀ k ∈ U, GeneralLinearGroup.map (pLoc E w) k = 1)
    (ψ : π.V) (h0 : ψ ≠ 0) (hψ : ψ ∈ fixed π.finPart U) :
    ∃ y : π.V, y ≠ 0 ∧ y ∈ fixed π.finPart U ∧ y ∈ fixed (π.locRep w) (KGL w (n := n)) := by
  by_contra hno
  have hsm : IsSmooth (π.locRep w) := fun v =>
    (π.isSmooth_finPart v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)
  have hc : IsCompact (KGL w (n := n) : Set (GLw n w)) := (Asm.unitHecke E n 0 0 w).2.2.2.1
  have hbot : fixed π.finPart U ⊓ fixed (π.locRep w) (KGL w (n := n)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
    by_contra hy0
    exact hno ⟨y, hy0, hy.1, hy.2⟩
  have hst : ∀ g, ∀ v ∈ fixed π.finPart U, π.locRep w g v ∈ fixed π.finPart U := fun g v hv =>
    mem_fix.2 fun k hk => by rw [fin_comm_loc π w (hU k hk), mem_fix.1 hv k hk]
  have hle := le_nullPart hsm hc _ hst hbot
  rcases null_cases π w (KGL w (n := n)) with h | h
  · exact h0 (by simpa [h] using hle hψ)
  · obtain ⟨x, hx0, hxK, -⟩ := hB.exists_vec
    exact hx0 (eq_zero_of_mem_nullPart hsm hc hxK (h ▸ Submodule.mem_top))

private theorem finPart_val (π : CuspSub E n) (g : GL (Fin n) (Af E)) (y : π.V) :
    (π.finPart g y : Sm E n) = finRep E n g y.1 := rfl

private theorem locRep_val (π : CuspSub E n) (w : Pl E) (a : GLw n w) (y : π.V) :
    (π.locRep w a y : Sm E n) = finRep E n (locGL E n w a) y.1 := rfl

private def fixer (y : Sm E n) : Subgroup (GL (Fin n) (Af E)) where
  carrier := {g | finRep E n g y = y}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    rw [Set.mem_setOf_eq] at ha ⊢
    have h : finRep E n a⁻¹ (finRep E n a y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

end SlopeTestRemainingChoices

theorem jointFix_pf : SlotBasic → JointFix := by
  intro _ E _ _ _ n π P
  classical
  induction P using Finset.induction_on with
  | empty =>
    rintro - U - ⟨ψ, h1, h2, h3⟩
    exact ⟨ψ, h1, h2, h3, by simp⟩
  | insert w P hw ih =>
    rintro hsat U hU ⟨ψ, hψ, h0, hfix⟩
    obtain ⟨B, hB⟩ := hsat w (Finset.mem_insert_self _ _)
    obtain ⟨y, hy0, hyU, hyK⟩ := step π w B hB U (fun k hk => hU k hk w (Finset.mem_insert_self _ _)) ⟨ψ, hψ⟩
      (fun e => h0 (congrArg Subtype.val e))
      (mem_fix.2 fun k hk => Subtype.ext ((finPart_val π k ⟨ψ, hψ⟩).trans (hfix k hk)))
    have hU' : ∀ k ∈ U ⊔ (KGL w (n := n)).map (locGL E n w), ∀ v ∈ P, qw n v false k = 1 := by
      intro k hk v hv
      have hvw : v ≠ w := fun e => hw (e ▸ hv)
      have hle : U ⊔ (KGL w (n := n)).map (locGL E n w) ≤ (qw (E := E) n v false).ker := by
        refine sup_le (fun c hc => MonoidHom.mem_ker.2 (hU c hc v (Finset.mem_insert_of_mem hv))) ?_
        rintro _ ⟨a, -, rfl⟩
        exact MonoidHom.mem_ker.2 (pLoc_locGL_of_ne hvw a)
      exact MonoidHom.mem_ker.1 (hle hk)
    have hy' : ∀ k ∈ U ⊔ (KGL w (n := n)).map (locGL E n w), finRep E n k y.1 = y.1 := by
      intro k hk
      have hle : U ⊔ (KGL w (n := n)).map (locGL E n w) ≤ fixer y.1 := by
        refine sup_le (fun c hc => ?_) ?_
        · exact (finPart_val π c y).symm.trans (congrArg Subtype.val (mem_fix.1 hyU c hc))
        · rintro _ ⟨a, ha, rfl⟩
          exact (locRep_val π w a y).symm.trans (congrArg Subtype.val (mem_fix.1 hyK a ha))
      exact hle hk
    obtain ⟨φ, hφ, hφ0, hφU, hφP⟩ := ih (fun v hv => hsat v (Finset.mem_insert_of_mem hv)) _ hU'
      ⟨y.1, y.2, fun e => hy0 (Subtype.ext e), hy'⟩
    refine ⟨φ, hφ, hφ0, fun k hk => hφU k (Subgroup.mem_sup_left hk), fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · exact mem_fix.2 fun a ha => hφU _ (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)
    · exact hφP v hv

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

private theorem hint_fst {G P : Type} [Group G] [Group P] [Subsingleton P] (K N : Subgroup G) (K' : Subgroup P)
    (u : G × P → ℂ) (hNK : N ≤ K) (hu : ∀ k ∈ N, ∀ x, u (x * k, 1) = u (x, 1)) (hi : N.relIndex K ≠ 0) :
    hint (K.prod K') u = ((N.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ N, u (q.out, 1) := by
  have hp : ∀ z : G × P, z = (z.1, 1) := fun z => Prod.ext rfl (Subsingleton.elim _ _)
  set L : Subgroup (G × P) := N.comap (MonoidHom.fst G P) with hL
  have hmap : (K.prod K').map (MonoidHom.fst G P) = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      exact ⟨(x, 1), ⟨hx, K'.one_mem⟩, rfl⟩
  have hrel : L.relIndex (K.prod K') = N.relIndex K := by
    rw [hL, Subgroup.relIndex_comap, hmap]
  have hLK : L ≤ K.prod K' := fun z hz => by
    rw [hp z]
    exact ⟨hNK hz, K'.one_mem⟩
  have hLu : L ≤ rStab u := fun k hk x => by
    have h1 : x * k = (x.1 * k.1, 1) := Prod.ext rfl (Subsingleton.elim _ _)
    rw [h1, hu k.1 hk x.1, ← hp x]
  rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ _ L u hLK hLu (by rwa [hrel]), hrel]
  congr 1
  have hval : ∀ q : G ⧸ N, u (Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) = u (q.out, 1) := by
    intro q
    have hm : ((q.out, (1 : P)))⁻¹ * Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) ∈ L :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    obtain ⟨k, hk⟩ : ∃ k : G × P, k ∈ L ∧ Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) = (q.out, 1) * k :=
      ⟨_, hm, (mul_inv_cancel_left _ _).symm⟩
    rw [hk.2]
    exact hLu hk.1 _
  have hbij : Function.Bijective (fun q : G ⧸ N => (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) := by
    constructor
    · intro a b hab
      have h := QuotientGroup.eq.mp hab
      have h2 : (a.out)⁻¹ * b.out ∈ N := by simpa [hL] using h
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      exact QuotientGroup.eq.mpr h2
    · intro c
      induction c using QuotientGroup.induction_on with
      | H z =>
        refine ⟨QuotientGroup.mk z.1, QuotientGroup.eq.mpr ?_⟩
        have h3 : ((QuotientGroup.mk z.1 : G ⧸ N).out)⁻¹ * z.1 ∈ N :=
          QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
        simpa [hL] using h3
  rw [← finsum_comp _ hbij]
  exact finsum_congr hval

private theorem tr_core (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := by
  set i : ℂ := ((N.relIndex K : ℕ) : ℂ) with hidef
  have hcvH : IsHecke N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) :=
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cvHecke _ N hNo hNc f₁ f₂ h₁ h₂
  have hFH : IsHecke N F := by
    refine ⟨?_, ?_⟩
    · rw [hFeq]
      exact hcvH.1.mul_left (f := fun _ => i⁻¹)
    · intro k hk x
      rw [hFeq]
      simp only
      rw [(hcvH.2 k hk x).1, (hcvH.2 k hk x).2]
      exact ⟨rfl, rfl⟩
  have hNK₁ : N ≤ K ⊓ rStab F ⊓ rStab fun y => F y⁻¹ := by
    refine le_inf (le_inf hNK ?_) ?_
    · exact fun k hk x => (hFH.2 k hk x).2
    · intro k hk x
      have e : (x * k)⁻¹ = k⁻¹ * x⁻¹ := by group
      show F (x * k)⁻¹ = F x⁻¹
      rw [e]
      exact (hFH.2 k⁻¹ (N.inv_mem hk) _).1
  have hK₁H : IsHecke (K ⊓ rStab F ⊓ rStab fun y => F y⁻¹) F := by
    refine ⟨hFH.1, fun k hk x => ⟨?_, hk.1.2 x⟩⟩
    have hk' : k⁻¹ ∈ rStab fun y => F y⁻¹ := (rStab _).inv_mem hk.2
    have := hk' x⁻¹
    simpa using this
  have hlev := hTr G K hKo hKc V ρ F _ N hNo hNK₁ (inf_le_left.trans inf_le_left) hK₁H hfd
  have hop : levOp ρ K N F LinearMap.id = i⁻¹ • i⁻¹ • levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id := by
    rw [hFeq]
    unfold levOp
    rw [Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    congr 1
    rw [smul_finsum]
    exact finsum_congr fun q => by rw [mul_smul]
  have hmul : ∀ v ∈ fixed ρ N, levOp ρ N N (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂) LinearMap.id v = (Lv ρ N f₁ * Lv ρ N f₂) v :=
    fun v hv => (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).1
  have hpres : ∀ v ∈ fixed ρ N, (Lv ρ N f₁ * Lv ρ N f₂) v ∈ fixed ρ N := fun v hv =>
    (hCv G N hNo hNc V ρ f₂ f₁ h₂ h₁ _ (hCv G N hNo hNc V ρ f₁ f₂ h₁ h₂ v hv).2.1).2.1
  have hstab : ∀ v ∈ fixed ρ N, levOp ρ K N F LinearMap.id v ∈ fixed ρ N := fun v hv => by
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v hv]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hpres v hv))
  have hres : (levOp ρ K N F LinearMap.id).restrict hstab = (i⁻¹ * i⁻¹) • (Lv ρ N f₁ * Lv ρ N f₂).restrict hpres := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [hop]
    simp only [LinearMap.smul_apply]
    rw [hmul v v.2, mul_smul]
  unfold trc
  rw [← hlev]
  unfold twTr trOn
  rw [dite_eq_left hstab, dite_eq_left hpres, hres, map_smul, smul_eq_mul]
  field_simp

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.seenTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → SeenTr := by
  intro hTr hAdm hCv E _ _ _ n w hw τ N hNo hNK
  obtain ⟨-, -, hKo, hKc, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w
  have hNc : IsCompact (N : Set (GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  haveI : Finite ((KGL w (n := n) : Subgroup (GLw n w)) ⧸ N.subgroupOf (KGL w (n := n))) :=
    GlobalTheory.TwTrLevel.finite_quot (KGL w (n := n)) (KGL w (n := n)) N hKc hKo hNo le_rfl
  have hi : N.relIndex (KGL w (n := n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiC : ((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  refine ⟨((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ^ 2, pow_ne_zero _ hiC, ?_⟩
  intro φ₁ φ₂ hb
  refine tr_core hTr hCv τ.ρ (KGL w (n := n)) N hKo hKc hNo hNc hNK hiC (hAdm E n w τ N hNo) _ _ _ (hb false) (hb true) ?_
  funext g
  have h₁ := hb false
  have h₂ := hb true
  have hr : ∀ k ∈ N, ∀ x : GLw n w, two φ₁ φ₂ w false (x * k) * two φ₁ φ₂ w true ((x * k)⁻¹ * g) =
      two φ₁ φ₂ w false x * two φ₁ φ₂ w true (x⁻¹ * g) := by
    intro k hk x
    have e : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    rw [e, (h₁.2 k hk x).2, (h₂.2 k⁻¹ (N.inv_mem hk) _).1]
  have hcv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N (two φ₁ φ₂ w false) (two φ₁ φ₂ w true) g =
      ∑ᶠ q : GLw n w ⧸ N, two φ₁ φ₂ w false q.out * two φ₁ φ₂ w true (q.out⁻¹ * g) := by
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
    rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ N N _ le_rfl (fun k hk x => hr k hk x) (by simp)]
    simp
  have hpr : ∀ x : GLw n w, ((x, 1) : GLw n w × GLw 0 w)⁻¹ * (g, 1) = (x⁻¹ * g, 1) := fun x =>
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [hcv]
  unfold PositivityTheory.Rg.BcB.G8.seen
  rw [if_pos hw]
  rw [hint_fst (KGL w (n := n)) N (KGL w (n := 0)) _ hNK ?_ hi]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [hpr]
    rfl
  · intro k hk x
    rw [hpr, hpr]
    exact hr k hk x
end
