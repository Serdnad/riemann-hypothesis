module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle009
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.ci_closed (l : ℕ) [Fact l.Prime] (x y : PadicAlgCl l) :
    IsClosed {σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l | σ x = y} := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hx
  have hU := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ := by fun_prop
  have h1 := (hU.preimage hc).mem_nhds (x := σ) (by simp)
  refine Filter.mem_of_superset h1 fun τ hτ h => hσ ?_
  have h2 : (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)
  have h3 : τ x = y := h
  have h4 : σ ((σ⁻¹ * τ) x) = τ x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  show σ x = y
  rw [← h3, ← h4, h2]

private theorem UpperTheory.V.Loc.ci_dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

private theorem UpperTheory.V.Loc.ci_pow_congr {K : Type*} [Monoid K] {x : K} {M a b : ℕ} (hx : x ^ M = 1)
    (h : a ≡ b [MOD M]) : x ^ a = x ^ b := by
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]

private theorem UpperTheory.V.Loc.ci_crt (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (M : ℕ) (hM : M ≠ 0) :
    ∃ c : ℕ, c.Coprime M ∧ c ≡ 1 [MOD ordCompl[l] M] ∧
      ∀ k ≤ M.factorization l, (c : ZMod (l ^ k)) = PadicInt.toZModPow k (a : ℤ_[l]) := by
  have hp : l.Prime := Fact.out
  set v := M.factorization l with hv
  have hcop : Nat.Coprime (ordCompl[l] M) (l ^ v) := (Nat.coprime_ordCompl hp hM).symm.pow_right _
  haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, h1, h2⟩ := Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val
  have hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]
  have hcoP : c.Coprime (l ^ v) := by
    rw [← ZMod.isUnit_iff_coprime, hc]
    exact (Units.isUnit a).map _
  have hcoN : c.Coprime (ordCompl[l] M) := by
    unfold Nat.Coprime
    rw [h1.gcd_eq, Nat.gcd_one_left]
  refine ⟨c, ?_, h1, fun k hk => ?_⟩
  · have := Nat.Coprime.mul_right hcoP hcoN
    rwa [hv, Nat.ordProj_mul_ordCompl_eq_self] at this
  · have hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l]) := by
      rw [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]
    have := (pow_dvd_pow _ hk).trans hd
    rwa [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast] at this

private theorem UpperTheory.V.Loc.ci_fin (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (n : ℕ) :
    ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l),
      (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val := by
  have hp : l.Prime := Fact.out
  obtain ⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)
  have hv : n ≤ M.factorization l :=
    (hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)
  obtain ⟨c, hcM, hc1, hc2⟩ := UpperTheory.V.Loc.ci_crt l a M hM0
  have hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N] := by
    intro N h
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  obtain ⟨σ, hσ⟩ := (UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0
    (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)
  have hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c := by
    intro d ⟨e, he⟩ x hx
    have hxM : x ^ M = 1 := by rw [he, pow_mul, hx, one_pow]
    rw [hσ x hxM]
    exact UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)
  refine ⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩
  · have hmM : m ∣ M := by
      rw [hM]
      exact (Nat.dvd_factorial hm0 hm).mul_right _
    have hm' : m ∣ ordCompl[l] M := Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm
    rw [hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]
  · have hkM : l ^ k ∣ M := by
      rw [hM]
      exact (pow_dvd_pow _ hk).mul_left _
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [hσc _ hkM x hx]
    refine UpperTheory.V.Loc.ci_pow_congr hx ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact hc2 k (le_trans hk hv)

private theorem UpperTheory.V.Loc.ci_surj (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) : ∃ g ∈ Iq l, cyc l l g = a := by
  have hp : l.Prime := Fact.out
  let S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) := fun n =>
    {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        UpperTheory.V.Loc.ci_closed l _ _
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩)
    (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩
  · unfold MaximalUnramifiedExtension at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm0, hlm, hx⟩ := hx
      exact (hσ m).1 m le_rfl hm0 hlm x hx
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)
    have h1 := cyclotomicCharacter.spec l (n := k)
      (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one
    have h2 := (hσ k).2 k le_rfl η hη.pow_eq_one
    have h3 := h1.symm.trans h2
    exact ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

private theorem UpperTheory.V.Loc.ci_inf (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one,
    Nat.pow_eq_one] at h2
  have := hp.one_lt
  omega

theorem UpperTheory.V.Loc.cycInertia :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l]ˣ, ∃ g ∈ Iq l, cyc l l g = u) ∧ ∀ U : Subgroup (GQ l), IsOpen (U : Set (GQ l)) → IsOpen (((U ⊓ Iq l).map (cyc l l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ∧ ∃ s ∈ U ⊓ Iq l, ¬ IsOfFinOrder (cyc l l s) := by
  intro l _
  refine ⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  constructor
  · have hs : Function.Surjective ((cyc l l).comp (Iq l).subtype) := fun u => by
      obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
      exact ⟨⟨g, hg⟩, h⟩
    have he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype) := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by
      rw [he]
      exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((U.isClosed_of_isOpen hU).inter
      (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed
  · obtain ⟨u, hu⟩ := UpperTheory.V.Loc.ci_inf l
    obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    refine ⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩
    rw [map_pow, h] at hf
    exact hf.of_pow hn.ne'
end

section

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module

structure LocalPublishedTheorems : Prop where
  lfK : Formalism.GaloisCohomology.LocalFinitenessK
  ltK : Formalism.GaloisCohomology.LocalTateDualityK
  leK : Formalism.GaloisCohomology.LocalEulerCharK
  lf : ReciprocityTheory.Gal.LocalFiniteness
  lt : ReciprocityTheory.Gal.LocalTateDuality
  le : ReciprocityTheory.Gal.LocalEulerChar
  bk : GlobalTheory.Published.BlochKatoLocal

section Rep

variable {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V]

def twist (κ : G →* Aˣ) (ρ : Representation A G V) : Representation A G V where
  toFun g := ((κ g : Aˣ) : A) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext x
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, mul_smul]
    rw [smul_comm]

def H0dual (χ : G →* Aˣ) (ρ : Representation A G V) : Submodule A (Module.Dual A V) where
  carrier := {f | ∀ g x, f (ρ g x) = ((χ g : Aˣ) : A) * f x}
  zero_mem' := fun g x => by simp
  add_mem' := fun {f f'} hf hf' g x => by simp only [LinearMap.add_apply, hf g x, hf' g x, mul_add]
  smul_mem' := fun c f hf g x => by simp only [LinearMap.smul_apply, hf g x, smul_eq_mul, mul_left_comm]

def FiltBy (ρ : Representation A G V) (S : Set (G →* Aˣ)) : Prop :=
  ∃ (n : ℕ) (F : ℕ → Submodule A V), F 0 = ⊥ ∧ F n = ⊤ ∧ ∀ i < n, F i ≤ F (i + 1) ∧
    ∃ κ ∈ S, ∃ x, F (i + 1) = F i ⊔ Submodule.span A {x} ∧ ∀ g, ρ g x - ((κ g : Aˣ) : A) • x ∈ F i

def UpperTri {n : ℕ} (r : G →* GL (Fin n) A) (κ : Fin n → G →* Aˣ) : Prop :=
  ∀ g, (∀ i j, j < i → (r g : Matrix (Fin n) (Fin n) A) i j = 0) ∧
    ∀ i, (r g : Matrix (Fin n) (Fin n) A) i i = ((κ i g : Aˣ) : A)

def conjGL {n : Type} [Fintype n] [DecidableEq n] (h : GL n A) (r : G →* GL n A) : G →* GL n A :=
  (MulAut.conj h).toMonoidHom.comp r

end Rep

section admitted

variable {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (ρ : Representation A G V)

def IsCr : Prop :=
  finrank ℚ_[l] ↥(Dcr φ (resCoef ℚ_[l] ρ)) = (φ.range ⊔ Iq l).index * finrank ℚ_[l] V

def IsDr : Prop :=
  finrank ℚ_[l] ↥(Ddr φ (resCoef ℚ_[l] ρ)) = φ.range.index * finrank ℚ_[l] V

def CrOn (H : Subgroup G) : Prop := IsCr (φ.comp H.subtype) (ρ.comp H.subtype : Representation A H V)

end admitted

def Positive {l : ℕ} [Fact l.Prime] {G E V : Type} [Group G] [TopologicalSpace G] [Field E] [Algebra ℚ_[l] E]
    [Algebra ℤ_[l] E] [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V]
    (φ : G →* GQ l) (ρ : Representation E G V) : Prop :=
  IsDr φ ρ ∧ FiltBy ρ {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w}

def QCont (l : ℕ) [Fact l.Prime] {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] (f : X → V) :
    Prop := @Continuous X V _ (moduleTopology ℚ_[l] V) f

end UpperTheory.V.Loc
end
end
