module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle089
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle002
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem frame_stab {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (ξ : Gp →* GL (Fin d) ℂ) (τ : X.Ub →* GL (Fin m) ℂ) (U : Subgroup X.Ub) (b : Gp) (F : Fin m → X.Fn ℂ d)
    (hF : F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.rpF ℂ d m b F ∈ Submodule.pi Set.univ (fun _ : Fin m => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i hi γ g => ?_, fun u hu => ?_⟩
  · have h := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at h
    exact h
  · funext i g k
    have h := congrFun (congrFun (congrFun (hF.2 u hu) i) (g * (1, b))) k
    have e : g * (1, b) * ((u : Ga), 1) = g * ((u : Ga), 1) * (1, b) := by
      rw [mul_assoc, mul_assoc]
      simp
    change (Matrix.mulVec (τ u : Matrix (Fin m) (Fin m) ℂ) fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i = F i (g * (1, b)) k at h
    rw [e] at h
    exact h

private theorem big_stab {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) (v : H.V)
    (g : GLw n (H.Sl v)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atV d v g F ∈ H.Big ι ξ :=
  frame_stab H.X ξ (H.τC ι) H.UQ _ F hF

private theorem iso_of {H P N W : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup W] [Module ℂ W] {m d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] W)
    (T : (P → Fin d → ℂ) →ₗ[ℂ] Module.Dual ℂ W →ₗ[ℂ] N) (ρ : Representation ℂ H (Fin m → P → Fin d → ℂ))
    (ρ' : Representation ℂ H N) (Y : Submodule ℂ (Fin m → P → Fin d → ℂ)) (Z : Submodule ℂ N) (τ : SmIrr H)
    (hZ : IsoSum ρ' Z τ) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hm : ∀ y ∈ Y, ∀ i ℓ, T (y i) ℓ ∈ Z)
    (he : ∀ y g i ℓ, T (ρ g y i) ℓ = ρ' g (T (y i) ℓ)) (hi : ∀ y ∈ Y, ∀ i, (∀ ℓ, T (y i) ℓ = 0) → y i = 0) :
    IsoSum ρ Y τ := by
  let b := (Pi.basisFun ℂ (Fin d)).map e
  refine UpperTheory.isoSum_of_injective_equivariant_family H _ N ρ ρ' Y Z τ (Fin m × Fin d)
    (fun x => T.flip (b.coord x.2) ∘ₗ LinearMap.proj x.1) hZ hY (fun x y hy => hm y hy x.1 _)
    (fun x g y _ => he y g x.1 _) fun y hy h => funext fun i => hi y hy i fun ℓ => ?_
  have h0 : T (y i) = 0 := b.dualBasis.ext fun k => by
    rw [Module.Basis.coe_dualBasis]
    exact h (i, k)
  rw [h0]
  rfl

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by
      simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by
      simp only [toForm, Pi.smul_apply, map_smul])
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoL :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∀ (v : V.frame.Vl) (τ : SmIrr (GLw n (s.w v.1))), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ → IsoSum (H := GLw n (s.w v.1)) ((hset Q τ₀).atV d v) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ v τ hτ
  have hsp : IsSplitAt (s.w v.1) :=
    UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A v.1) v.1 (s.hA v.1) (s.split v.1 (Or.inl v.2)) _ (w_under s v.1)
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn (s.w v.1) hsp).1
  have hZ := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ (s.w v.1) j hj1 hj2 hj3 τ hτ
  have hM := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hA := partUR2AtV l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ v j hj1 hj2
  have hI := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  have hY : ∀ g, ∀ y ∈ YOf Q ι τ₀ e ξ σ, (hset Q τ₀).atV d v g y ∈ YOf Q ι τ₀ e ξ σ := fun g y hy =>
    (hM _).2 ⟨big_stab (hset Q τ₀) ι ξ v g y ((hM y).1 hy).1, fun i ℓ =>
      (hA y g i ℓ).symm ▸ hσ.stable (j g) _ (((hM y).1 hy).2 i ℓ)⟩
  exact iso_of (H := GLw n (s.w v.1)) (m := m) e (formLin ι e) ((hset Q τ₀).atV d v) ((RU L n).comp j) (YOf Q ι τ₀ e ξ σ) σ τ hZ hY
    (fun y hy => ((hM y).1 hy).2) hA fun y hy i h => hI (y i) (((hM y).1 hy).1.1 i trivial) h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


noncomputable section

namespace UpperTheory.V.Hi.LvR

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

theorem c1 (i) : (rUp h).chib i = (r.chib i).comp (fh h).π₀ := rfl

theorem rUp_chib (i) (g : V.frame.G₀) : (rUp h).chib i g = r.chib i (p0 h g) := MonoidHom.comp_apply (r.chib i) (p0 h) g

theorem c2 (v i) : (rUp h).psib v i = (r.psib ((fh h).vl v) i).comp ((fh h).gv v) := MonoidHom.ext fun _ => rfl

theorem c3 (v i) (g : V.frame.mu v) (hg : (fh h).gv v g ∈ V0.frame.mu ((fh h).vl v)) : (rUp h).th v i g = r.th ((fh h).vl v) i ⟨_, hg⟩ := by
  have e : ∀ g : W.muG l (Dec (F := L) (s.A v.1)), (rUp h).th v i g = @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g := fun _ => rfl
  have e2 : ∀ (g : Dec (F := L) (s.A v.1)) (hg : g ∈ W.muG l (Dec (F := L) (s.A v.1))), @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) ⟨g, hg⟩ = r.th v i ⟨g, hg⟩ := fun _ _ => rfl
  exact (e g).trans (e2 g.1 (@id (g.1 ∈ W.muG l (Dec (F := L) (s.A v.1))) g.2))

theorem c4 (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (u : s.St) (g : V.η.ker) (hg : g ∈ (rUp h).Ip u) : p0 h g ∈ r.Ip u := by
    obtain ⟨⟨x, hx, rfl⟩, h2⟩ := hg
    refine ⟨⟨x, hx, (levelChangeBaseGroupHom_apply_projection h hp x).symm⟩, ?_⟩
    exact Subgroup.mem_iInf.2 fun i => MonoidHom.mem_ker.2 ((rUp_chib h i _).symm.trans (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 h2 i)))

theorem rUp_compat (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) : (fh h).Compat (rUp h) r :=
  ⟨c1 h, c2 h, c3 h, fun u g hg => Or.inr ⟨u, c4 h hp u g hg⟩⟩

theorem pairUp (hn : 1 ≤ n) (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) :
    ∃ p' : Pair (rUp h) R, p'.D = p.D.comap (p0 h) ∧ ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* Rˣ) (p'.ψ v i) (p.ψ v i) := by
  obtain ⟨p', h1, h2⟩ := W.exists_determinantPair_pullback l _ _ (fh h) O n (rUp h) r (rUp_compat h hp) (fun e => by omega) R p
  exact ⟨p', h1, fun v i => Eq.trans (h2 v i) rfl⟩

end Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

abbrev qUp (V : s.Lev) {q : ℕ} (w : Fin q → Plc L) (h1 : Function.Injective fun j => (w j).under (𝓞 (Lp L)))
    (h2 : ∀ j, (w j).under (𝓞 (Lp L)) ∉ s.S) (h3 : V.S' = s.S ∪ Set.range fun j => (w j).under (𝓞 (Lp L))) : QData V where
  Q := Fin q
  wq := w
  inj := h1
  notS := h2
  range := h3

variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')

def opUp {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Op → (hset Q0 τ₀).Op
  | .inl x => .inl (⟨x.1.1, fun h => x.1.2.1 (hS h), x.1.2.2⟩, x.2)
  | .inr x => .inr x

def kMax {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Lev :=
  ⟨fun _ => KO _ (Fin n), fun _ => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩

theorem free_of_neat {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  have e1 : ∀ hh, (⟨1, hh⟩ : X.I.T) = 1 := fun _ => rfl
  rw [e1, map_one, map_one]
  simp

theorem teich_ext {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (x y : Oˣ) (h : residue O x = residue O y)
    (hx : x ^ (Nat.card (ResidueField O) - 1) = 1) (hy : y ^ (Nat.card (ResidueField O) - 1) = 1) : x = y := by
  set N := Nat.card (ResidueField O) - 1 with hN
  have hx' : (x : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hy' : (y : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have e := (Commute.all (x : O) y).geom_sum₂_mul N
  rw [hx', hy', sub_self] at e
  have hu : IsUnit (∑ i ∈ Finset.range N, (x : O) ^ i * (y : O) ^ (N - 1 - i)) := by

    rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range N, residue O ((x : O) ^ i * (y : O) ^ (N - 1 - i)) = residue O y ^ (N - 1) := fun i hi => by
      rw [map_mul, map_pow, map_pow, h, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_ne_zero ?_ (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).2 y.isUnit))
    haveI := Fintype.ofFinite (ResidueField O)
    rw [hN, Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    simp
  exact Units.ext (sub_eq_zero.1 (hu.mul_right_eq_zero.1 e))

theorem typeFor_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : TypeFor r ι τ₀) : TypeFor (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this

theorem cont_up {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) {A : Type} [CommRing A] [IsLocalRing A]
    (θ : (hset Q0 τ₀).X.I.T →* Aˣ) (hθ : (hset Q0 τ₀).X.I.ContChar θ) : (hset Q τ₀).X.I.ContChar θ := hθ

theorem res_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (a : (hset Q0 τ₀).Op → c.O) (ha : IsRes Q0 r τ₀ a) : IsRes Q (rUp h) τ₀ fun i => a (opUp Q0 Q hS τ₀ i) := by
  refine ⟨fun w B σ hB hσ => ?_, ?_⟩
  · refine (congrArg (fun D : W.GDet n (ResidueField c.O) V.frame.G₀ => D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1))
      (rUp_Dbar h)).trans ((chi_comap r.Dbar (p0 h) (V.pr σ⁻¹)).trans ?_)
    exact (congrArg (fun g : V0.frame.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) (levelChangeBaseGroupHom_apply_projection h hp σ⁻¹)).trans
      (ha.frob ⟨w.1, fun h => w.2.1 (hS h), w.2.2⟩ B σ hB hσ)
  · have := ha.unif
    cases r
    exact this


end UpperTheory.V.Hi.LvR
end
end
