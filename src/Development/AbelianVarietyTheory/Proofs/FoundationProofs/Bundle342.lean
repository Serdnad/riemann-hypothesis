module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle174
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCardLen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoScal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

namespace GlobalTheory.FinTwoMembership

open Matrix

theorem mem_of_fin_two {R : Type*} [CommRing R] (S : Subring R) (M : Matrix (Fin 2) (Fin 2) R)
    (y z : Fin 2 → R) (u : R) (hM : ∀ i j, M i j ∈ S) (hy : ∀ i, y i ∈ S) (hz : ∀ i, z i ∈ S)
    (hu : u ∈ S) :
    M.det * u - ((M.adjugate *ᵥ y) 0 * z 1 - (M.adjugate *ᵥ y) 1 * z 0) ∈ S := by
  have hadj : ∀ i j, M.adjugate i j ∈ S := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [S.neg_mem, hM]
  have hv : ∀ i, (M.adjugate *ᵥ y) i ∈ S := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact S.add_mem (S.mul_mem (hadj _ _) (hy _)) (S.mul_mem (hadj _ _) (hy _))
  have hdet : M.det ∈ S := by
    rw [Matrix.det_fin_two]
    exact S.sub_mem (S.mul_mem (hM _ _) (hM _ _)) (S.mul_mem (hM _ _) (hM _ _))
  exact S.sub_mem (S.mul_mem hdet hu)
    (S.sub_mem (S.mul_mem (hv _) (hz _)) (S.mul_mem (hv _) (hz _)))

theorem ht_mem : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
    (c : UpperTheory.V.HV.Coef l) (W : GlobalTheory.Ord2.R2 Ω l) (y z : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)
    (u : Formalism.ConjugateSelfDual.G ℚ Ω → Formalism.ConjugateSelfDual.Qbar l),
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i j : Fin (2 : ℕ)), GlobalTheory.Ord2.mat W s i j ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), y s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), z s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), u s ∈ UpperTheory.V.HV.Coef.O c) →
    ∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), GlobalTheory.Ord2.ht W y z u s ∈ UpperTheory.V.HV.Coef.O c := by
  intro Ω _ _ l _ c W y z u hW hy hz hu s
  have hM : ∀ i j, (GlobalTheory.Ord2.mat W s - 1) i j ∈ c.O.toSubring := by
    intro i j
    rw [Matrix.sub_apply]
    refine c.O.toSubring.sub_mem (hW s i j) ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact c.O.toSubring.one_mem
    · exact c.O.toSubring.zero_mem
  exact mem_of_fin_two c.O.toSubring _ (y s) (z s) (u s) hM (hy s) (hz s) (hu s)

end GlobalTheory.FinTwoMembership
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.IrrConj

theorem isIrrSub_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ}
    (H H' : Subgroup Γ) (hH : ∀ s, s ∈ H → s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsIrrSub (r.comp H.subtype) ⊤) : IsIrrSub (r'.comp H'.subtype) ⊤ := by
  first
  | exact @_root_.GlobalTheory.ConjugateIrreducibility.target
  | exact _root_.GlobalTheory.ConjugateIrreducibility.target
  | (apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateIrreducibility.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateIrreducibility.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateIrreducibility.target ..)

theorem dt_eq_of_repIso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (W W' : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (hg : ∀ s, W' s = g * W s * g⁻¹) (s : G ℚ Ω) :
    dt W' s = dt W s := by
  simp only [dt, MonoidHom.comp_apply, hg s, map_mul, map_inv]
  rw [mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc, mul_inv_cancel, mul_one]

theorem irr_of_repIso : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (W W' : R2 Ω l),
    RepIso W W' → IsIrr (W.comp (H0g W).subtype) → IsIrr (W'.comp (H0g W').subtype) := by
  intro Ω _ _ l _ W W' ⟨g, hg⟩ h
  refine isIrrSub_conj (H0g W) (H0g W') ?_ W W' g hg h
  intro s hs
  simp only [H0g, Subgroup.mem_inf, MonoidHom.mem_ker] at hs ⊢
  exact ⟨hs.1, by rw [dt_eq_of_repIso W W' g hg]; exact hs.2⟩

end GlobalTheory.IrrConj
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocChar

private def repOverZMod {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (N : ℕ)
    [Module (ZMod N) M] (ρ : Representation O Γ M) : Representation (ZMod N) Γ M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap N
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul, Module.End.mul_apply]

theorem local_character_h1_bound : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → (∃ g, θ g ≠ 1) → (∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ∧ Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) := by
  open Formalism.GaloisCohomology IsLocalRing UpperTheory.V.Base UpperTheory.V.X in
  set_option synthInstance.maxHeartbeats 200000 in
  intro hF hT hE l _ Ω _ _ _ c A hA θ hθc hne₁ hne₂
  obtain ⟨g₁, hne₁⟩ := hne₁
  obtain ⟨g₂, hne₂⟩ := hne₂
  obtain ⟨v, hv, hlv⟩ := hA
  have hd₁ : (θ g₁ : c.O) - 1 ≠ 0 := fun h => hne₁ (Units.ext (sub_eq_zero.1 h))
  have hd₂ : ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 ≠ 0 := fun h => hne₂ (by
    have h' : chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ = 1 := Units.ext (sub_eq_zero.1 h)
    rw [map_inv, mul_inv_eq_one] at h'
    exact h'.symm)
  set d₂ := ((chiO ℚ Ω l c.O (g₂ : G ℚ Ω) * θ g₂⁻¹ : c.Oˣ) : c.O) - 1 with hd₂def
  have hK : Finite (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))) := by
    rw [← ((So.cardLen l c.O).2 _).1, (qoFacts l c.O).2.2.2]
    exact fun h => hd₂ (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨Nat.card (c.O ⧸ Ideal.span {(θ g₁ : c.O) - 1}) *
    Nat.card (LinearMap.ker (d₂ • (LinearMap.id : QO l c.O →ₗ[c.O] QO l c.O))), fun n hn => ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have ha : ((l : ℕ) : c.O) ^ n ≠ 0 := pow_ne_zero _ hl0
  set a := ((l : ℕ) : c.O) ^ n with hadef
  obtain ⟨hM, ⟨r, hr, hkill⟩, htor⟩ := So.levFacts l c.O a ha (Lev a) ⟨LinearEquiv.refl c.O _⟩
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) (Lev a)) := ⟨AddCommGroup.zmodModule hkill⟩
  set ρ := Formalism.GaloisCohomology.scalRep (Lev a) θ with hρ
  let ρ' : Representation (ZMod (l ^ r)) (Dec (F := ℚ) A) (Lev a) := repOverZMod (l ^ r) ρ
  have hact : ∀ (g : Dec (F := ℚ) A) (m : Lev a), ρ' g m = (θ g : c.O) • m := fun g m => rfl
  have hc : ContAction ρ' := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    obtain ⟨x, rfl⟩ := Lev.mk_surjective a m
    have h1 : Continuous fun g : Dec (F := ℚ) A => Lev.mk a ((θ g : c.O) * x) :=
      ((So.adicCont l c).1 a ha).comp (hθc.mul continuous_const)
    refine h1.congr fun g => ?_
    show Lev.mk a ((θ g : c.O) * x) = (θ g : c.O) • Lev.mk a x
    rw [← smul_eq_mul, map_smul]
  obtain ⟨f1, -, c2⟩ := So.locCard hF hT ℚ Ω l r hr v A hv (Lev a) ρ' hc
    (twDual ((cycMod ℚ Ω l r).comp (Dec (F := ℚ) A).subtype) ρ') fun g φ m => twDual_apply _ _ _ _ _
  have he := (hE ℚ Ω l r (Lev a) A ρ' v hr hv hc).1 hlv
  rw [GlobalTheory.OrdLoc.Dcmp.locDeg_rat hlv, pow_one] at he
  obtain ⟨-, ⟨e1⟩, -⟩ := So.scal c.O (ZMod (l ^ r)) _ (Lev a) ρ ρ' fun _ _ => rfl
  refine ⟨Finite.of_equiv _ e1.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e1.toEquiv, he, c2]
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_trans ?_ (htor _ hd₁)) ?_) le_rfl
  · refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩)
      fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
    have := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 x.2 g₁
    rw [hact] at this
    exact (sub_smul _ _ _).trans (by rw [one_smul, this, sub_self])
  · obtain ⟨ι, hι, -, hιs⟩ := So.dualEmb l c.O a ha r (Lev a) ⟨LinearEquiv.refl c.O _⟩
    refine Nat.card_le_card_of_injective (fun x => ⟨ι x.1, ?_⟩)
      fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy))
    have hx := (Representation.mem_invariants _ _).1 x.2 g₂
    have := hιs (cycZ ℚ Ω l (g₂ : G ℚ Ω) : ℤ_[l]ˣ) ((θ g₂⁻¹ : c.Oˣ) : c.O) x.1 x.1 fun m => by
      conv_lhs => rw [← hx, twDual_apply, hact]
      rfl
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hd₂def, sub_smul, one_smul, sub_eq_zero]
    exact this.symm

end GlobalTheory.LocChar
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.LocCharPerfect

open UpperTheory.V.X

variable {l : ℕ} [Fact l.Prime]

theorem lev_kill (c : Coef l) (n : ℕ) (m : Lev ((l : c.O) ^ n)) : (l ^ n) • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_nsmul, Lev.mk_eq_zero, nsmul_eq_mul, Nat.cast_pow]
  exact dvd_mul_right _ _

def levZMod (c : Coef l) (n : ℕ) : Module (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
  AddCommGroup.zmodModule (lev_kill c n)

attribute [local instance] levZMod

theorem smul_eq_zero_of_dvd (c : Coef l) (n : ℕ) {d : c.O} (h : (l : c.O) ^ n ∣ d)
    (m : Lev ((l : c.O) ^ n)) : d • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_smul, Lev.mk_eq_zero, smul_eq_mul]
  exact h.mul_right _

theorem lev_sub_smul (c : Coef l) (n : ℕ) (x y : c.O) (m : Lev ((l : c.O) ^ n)) :
    (x - y) • m = x • m - y • m := sub_smul x y m

theorem smul_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : (l : c.O) ^ n ∣ x - y)
    (m : Lev ((l : c.O) ^ n)) : x • m = y • m := by
  rw [← sub_eq_zero, ← sub_smul]
  exact smul_eq_zero_of_dvd c n h m

theorem zmod_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (a : ZMod (l ^ n)) (m : Lev ((l : c.O) ^ n)) :
    a • m = ((a.val : ℕ) : c.O) • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem padic_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (z : ℤ_[l]) (m : Lev ((l : c.O) ^ n)) :
    algebraMap ℤ_[l] c.O z • m = PadicInt.toZModPow n z • m := by
  rw [zmod_smul]
  refine smul_congr c n ?_ m
  have hk : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨algebraMap ℤ_[l] c.O t, ?_⟩
  rw [← map_natCast (algebraMap ℤ_[l] c.O), ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_comm]

def scal (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) :
    Representation (ZMod (l ^ n)) Γ (Lev ((l : c.O) ^ n)) where
  toFun g := (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) ((χ g : c.Oˣ) : c.O)).toZModLinearMap (l ^ n)
  map_one' := LinearMap.ext fun m => by
    show ((χ 1 : c.Oˣ) : c.O) • m = m
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun m => by
    show ((χ (g * h) : c.Oˣ) : c.O) • m = ((χ g : c.Oˣ) : c.O) • ((χ h : c.Oˣ) : c.O) • m
    rw [map_mul, Units.val_mul, mul_smul]

theorem scal_apply (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) (g : Γ) (m : Lev ((l : c.O) ^ n)) :
    scal c n χ g m = ((χ g : c.Oˣ) : c.O) • m := rfl

def smulZ (c : Coef l) (n : ℕ) (x : c.O) : Lev ((l : c.O) ^ n) →ₗ[ZMod (l ^ n)] Lev ((l : c.O) ^ n) :=
  (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) x).toZModLinearMap (l ^ n)

theorem contAction_scal (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ' : Γ →* c.Oˣ)
    (hθ' : Continuous (fun g => ((θ' g : c.Oˣ) : c.O))) (n : ℕ) (h0 : ((l : c.O) ^ n) ≠ 0) :
    ContAction (scal c n θ') := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  refine (((UpperTheory.V.X.So.adicCont l c).1 _ h0).comp (hθ'.mul (continuous_const (y := x)))).congr fun g => ?_
  show Lev.mk ((l : c.O) ^ n) (((θ' g : c.Oˣ) : c.O) * x) = ((θ' g : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) x
  rw [← smul_eq_mul, map_smul]

end GlobalTheory.Ord2.LocCharPerfect


open GlobalTheory.Ord2.LocCharPerfect UpperTheory.V.X in
attribute [local instance] levZMod in

theorem GlobalTheory.Ord2.LocCharPerfect.perfect : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  intro hF hT l _ Ω _ _ _ c A hA θ θ' hθ hθ' hθθ n hn b hb hbc hcup
  classical
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have ha0 : ((l : c.O) ^ n) ≠ 0 := pow_ne_zero _ hl0
  obtain ⟨v, hv, -⟩ := hA
  haveI : Finite (Lev ((l : c.O) ^ n)) :=
    (UpperTheory.V.X.So.levFacts l c.O _ ha0 (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩).1
  obtain ⟨φ₀, hφ0, hφall⟩ := UpperTheory.V.X.So.dualGen l c.O _ ha0 n (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩
  set rho := scal c n θ' with hrho
  have hc : ContAction rho := contAction_scal c θ' hθ' n ha0
  set χ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) A).subtype with hχ

  have hchi : ∀ s : ↥(Dec (F := ℚ) A), ((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O) =
      algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (s : G ℚ Ω) : ℤ_[l]) := fun s => by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hθθ]; rfl
  have hχs : ∀ (s : ↥(Dec (F := ℚ) A)) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • m = (((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) • m := by
    intro s m
    rw [hchi, padic_smul]; rfl
  have key : ∀ (s : ↥(Dec (F := ℚ) A)) (x : c.O) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (x • rho s⁻¹ m) = φ₀ ((((θ s : c.Oˣ) : c.O) * x) • m) := by
    intro s x m
    rw [← smul_eq_mul, ← map_smul, hχs, scal_apply, smul_smul, smul_smul, map_inv]
    congr 2
    calc _ = (((θ s : c.Oˣ) : c.O) * x) * (((θ' s : c.Oˣ) : c.O) * (((θ' s)⁻¹ : c.Oˣ) : c.O)) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]

  let bs : ↥(Dec (F := ℚ) A) → TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
    fun s => TDual.mk (φ₀ ∘ₗ smulZ c n (b s))
  let sec := Function.surjInv (Lev.mk_surjective ((l : c.O) ^ n))
  have hsec : ∀ y, Lev.mk ((l : c.O) ^ n) (sec y) = y := Function.surjInv_eq _
  have hmk : Continuous (Lev.mk ((l : c.O) ^ n)) := (UpperTheory.V.X.So.adicCont l c).1 _ ha0
  have hbsc : Continuous bs := by
    refine ((continuous_of_discreteTopology (f := fun y : Lev ((l : c.O) ^ n) =>
      TDual.mk (φ₀ ∘ₗ smulZ c n (sec y)))).comp (hmk.comp hb)).congr fun s => ?_
    refine DFunLike.ext _ _ fun m => ?_
    show φ₀ (sec (Lev.mk ((l : c.O) ^ n) (b s)) • m) = φ₀ (b s • m)
    have hd : (l : c.O) ^ n ∣ sec (Lev.mk ((l : c.O) ^ n) (b s)) - b s := by
      rw [← Lev.mk_eq_zero, map_sub, hsec, sub_self]
    rw [smul_congr c n hd m]
  have hz : bs ∈ Z1 ((twDual χ rho).comp (MonoidHom.id _)) := by
    refine ⟨hbsc, fun s t => ?_⟩
    refine DFunLike.ext _ _ fun m => ?_
    show φ₀ (b (s * t) • m) = φ₀ (b s • m) + ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (b t • rho s⁻¹ m)
    rw [key, ← map_add (f := _), ← add_smul, smul_congr c n (hbc s t) m]
  obtain ⟨-, -, hbij, -, -⟩ := hT ℚ Ω l n (Lev ((l : c.O) ^ n)) A rho v (by omega) hv hc
  have h0 : (Submodule.Quotient.mk ⟨bs, hz⟩ : H1 ((twDual χ rho).comp (MonoidHom.id _))) = 0 := by
    refine hbij.1 (Eq.trans ?_ (LinearMap.map_zero _).symm)
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    let at' : ↥(Dec (F := ℚ) A) → c.O := fun t => sec (y.1 t)
    have hat : ∀ t, Lev.mk ((l : c.O) ^ n) (at' t) = y.1 t := fun t => hsec _
    have hac : Continuous at' := (continuous_of_discreteTopology (f := sec)).comp y.2.1
    have hacoc : ∀ s t, (l : c.O) ^ n ∣ at' (s * t) - (at' s + ((θ' s : c.Oˣ) : c.O) * at' t) := by
      intro s t
      have hm : Lev.mk ((l : c.O) ^ n) (((θ' s : c.Oˣ) : c.O) * at' t) = ((θ' s : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) (at' t) := by
        rw [← smul_eq_mul, map_smul]
      rw [← Lev.mk_eq_zero, map_sub, map_add (f := _), hm, hat, hat, hat, y.2.2 s t]
      exact sub_self _
    obtain ⟨u, hu, hdiv⟩ := hcup at' hac hacoc
    change (Submodule.Quotient.mk (cupCocycleZ1Z1 _ _ _ _ _ _ _ _ _) : H2 _) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨fun t => φ₀ (Lev.mk ((l : c.O) ^ n) (u t)),
      (continuous_of_discreteTopology (f := ⇑φ₀)).comp (hmk.comp hu), funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    have e1 : (((θ g : c.Oˣ) : c.O) * ((θ' g : c.Oˣ) : c.O)) • Lev.mk ((l : c.O) ^ n) (u h) -
        Lev.mk ((l : c.O) ^ n) (u (g * h)) + Lev.mk ((l : c.O) ^ n) (u g) =
        b g • ((θ' g : c.Oˣ) : c.O) • y.1 h := by
      rw [← hat h, ← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add (f := _), smul_eq_mul, smul_eq_mul,
        smul_eq_mul]
      have := (Lev.mk_eq_zero _ _).2 (hdiv g h)
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    show ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (Lev.mk ((l : c.O) ^ n) (u h)) -
      φ₀ (Lev.mk ((l : c.O) ^ n) (u (g * h))) + φ₀ (Lev.mk ((l : c.O) ^ n) (u g)) =
      φ₀ (b g • ((θ' g : c.Oˣ) : c.O) • y.1 h)
    rw [← e1, map_add (f := _), map_sub, ← hχs, map_smul, smul_eq_mul]
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨ψ, hψ⟩ := (mem_coboundaries1 _ _).1 (Submodule.mem_comap.1 h0)
  obtain ⟨x, hx⟩ := hφall ψ
  refine ⟨x, fun s => (hφ0 _).1 fun m => ?_⟩
  have e := congrArg (fun φ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) => φ m) (hψ s)
  change φ₀ (b s • m) = ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * ψ (rho s⁻¹ m) - ψ m at e
  have hx' : ∀ m, (ψ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n))) m = φ₀ (x • m) := hx
  rw [hx', hx', key] at e
  have h1 : (b s - (((θ s : c.Oˣ) : c.O) * x - x)) • m = b s • m - ((((θ s : c.Oˣ) : c.O) * x) • m - x • m) := by
    rw [lev_sub_smul, lev_sub_smul]
  refine (congrArg φ₀ h1).trans ?_
  rw [map_sub, map_sub, e, sub_self]
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.GwCount

theorem cocycle_zero_on_ker_toGS : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (Y : G ℚ Ω → Fin 2 → Qbar l), Nf e S A W → Y ∈ Z1 (Loc.colRep W) → (∀ q : Pl, q ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, Y s = mat W s *ᵥ x - x) → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Y a = 0 := by
  intro l _ Ω _ _ _ e S A W Y hN hY hc a ha
  have hcoc : ∀ g h, Y (g * h) = Y g + mat W g *ᵥ Y h := fun g h => ((mem_Z1_iff_cocycle _ _).1 hY).2 g h
  have hcont : Continuous Y := ((mem_Z1_iff_cocycle _ _).1 hY).1
  have h1 : Y 1 = 0 := by
    have := hcoc 1 1
    simpa [mat] using this
  let H : Subgroup (G ℚ Ω) :=
    { carrier := {g | Y g = 0 ∧ W g = 1}
      one_mem' := ⟨h1, map_one W⟩
      mul_mem' := fun {g h} hg hh => ⟨by rw [hcoc, hg.1, hh.1]; simp, by rw [map_mul, hg.2, hh.2, one_mul]⟩
      inv_mem' := fun {g} hg => by
        refine ⟨?_, by rw [map_inv, hg.2, inv_one]⟩
        have := hcoc g g⁻¹
        rw [mul_inv_cancel, h1, hg.1] at this
        simpa [mat, hg.2] using this.symm }
  have hH : ∀ g, g ∈ H ↔ Y g = 0 ∧ W g = 1 := fun g => Iff.rfl
  haveI : H.Normal := ⟨fun g hg h => by
    rw [hH] at hg ⊢
    refine ⟨?_, by rw [map_mul, map_mul, hg.2, mul_one, ← map_mul, mul_inv_cancel, map_one]⟩
    have e1 : Y (g * h⁻¹) = Y h⁻¹ := by
      rw [hcoc, hg.1]; simp [mat, hg.2]
    rw [mul_assoc, hcoc, e1, ← hcoc, mul_inv_cancel, h1]⟩
  have hcl : IsClosed (H : Set (G ℚ Ω)) :=
    (isClosed_singleton.preimage hcont).inter (isClosed_singleton.preimage hN.cont)
  have hle : Subgroup.normalClosure
      (⋃ v ∈ (S : Set Pl)ᶜ, ⋃ B ∈ {B : ValuationSubring Ω | IsPlaceOver B v}, Inertia (F := ℚ) B) ≤ H := by
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    have hv' : v ∉ S := by simpa using hv
    have hτ' : τ ∈ Ine (F := ℚ) B := hτ
    have hW : W τ = 1 := hN.unr v hv' B hB hτ'
    obtain ⟨x, hx⟩ := hc v hv' B hB
    refine (hH τ).2 ⟨?_, hW⟩
    rw [hx τ hτ']
    simp [mat, hW]
  have ha' : a ∈ NS Ω (S : Set Pl) := by
    rwa [toGS, QuotientGroup.ker_mk'] at ha
  exact ((hH a).1 (Subgroup.topologicalClosure_minimal _ hle hcl ha')).1

end GlobalTheory.Ord2.GwCount
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.DualCont

theorem cyc_cont' {Ω : Type} [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem units_cont {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

theorem continuous_galoisRepRankTwoTateDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  intro l _ Ω _ _ _ e S A W hN
  have hW : Continuous fun s => ((W s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp hN.cont
  have hd : Continuous (dt W) := by
    apply units_cont
    show Continuous fun s => (Matrix.GeneralLinearGroup.det (W s) : Qbar l)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hW.matrix_det
  have hc := cyc_cont' (Ω := Ω) l
  have hχ : Continuous (cycBar ℚ Ω l * (dt W)⁻¹) := by
    show Continuous fun s => cycBar ℚ Ω l s * ((dt W) s)⁻¹
    exact hc.mul hd.inv
  apply units_cont
  show Continuous fun s => ((tw W (cycBar ℚ Ω l * (dt W)⁻¹) s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
  simp only [tw_val]
  exact (Units.continuous_val.comp hχ).smul hW

end GlobalTheory.Ord2.DualCont
end
end
