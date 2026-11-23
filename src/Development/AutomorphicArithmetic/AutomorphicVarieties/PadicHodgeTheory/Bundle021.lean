module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle068
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle008
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
public import Mathlib.Algebra.Module.PID
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
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
import Mathlib.LinearAlgebra.FreeProduct.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc

private theorem ul_exp_onto {A : Type} [CommRing A] [Algebra ℚ A] {n : A} (hn : IsNilpotent n) :
    ∃ x, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n :=
  _root_.UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto hn

private theorem t2Space_finite_padic_module {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module.Finite ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : T2Space V := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  let e0 := (Module.finBasis ℚ_[l] V).equivFun
  exact T2Space.of_injective_continuous e0.injective
    (IsModuleTopology.continuous_of_linearMap e0.toLinearMap)

theorem UpperTheory.lift_unramified_unipotent_character :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] (p : B →ₐ[ℚ_[l]] B'), Function.Surjective p → (∀ a, p a = 0 → IsNilpotent a) → ∀ u' : GQ v →* B'ˣ, QCont l (fun g => (u' g : B')) → (∀ g ∈ Iq v, u' g = 1) → (∀ g, IsNilpotent ((u' g : B') - 1)) → ∃ u : GQ v →* Bˣ, QCont l (fun g => (u g : B)) ∧ (∀ g ∈ Iq v, u g = 1) ∧ ∀ g, p (u g : B) = (u' g : B') := by
  intro v l _ _ B B' _ _ _ _ _ _ p hp hker u' hc' hI' hn'
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : IsTopologicalAddGroup B' := IsModuleTopology.topologicalAddGroup ℚ_[l] B'
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B' := IsModuleTopology.toContinuousSMul ℚ_[l] B'
  haveI : T2Space B' := t2Space_finite_padic_module (l := l)
  obtain ⟨σ, hσ⟩ := (iqBasic v).2.2.2.1
  obtain ⟨x', hx', he'⟩ := ul_exp_onto (hn' σ)
  obtain ⟨x, rfl⟩ := hp x'
  have hx : IsNilpotent x := by
    obtain ⟨k, hk⟩ := hx'
    exact (hker (x ^ k) (by rw [map_pow, hk])).of_pow
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ v) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  let f : GQ v →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ v → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq v, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_⟩
  let f1 : GQ v →* B' := (p : B →* B').comp f
  let f2 : GQ v →* B' := (Units.coeHom B').comp u'
  have hcl : IsClosed ((f1.eqLocus f2 : Subgroup (GQ v)) : Set (GQ v)) :=
    isClosed_eq ((IsModuleTopology.continuous_of_linearMap p.toLinearMap).comp hf) hc'
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ f1.eqLocus f2 := by
    refine sup_le (fun k hk => ?_) ((Subgroup.zpowers_le).2 ?_)
    · change p (f k) = (u' k : B')
      rw [hfI k hk, hI' k hk, map_one, Units.val_one]
    · change p (IsNilpotent.exp (c σ • x)) = (u' σ : B')
      rw [hcσ, one_smul, IsNilpotent.map_exp hx, he', add_sub_cancel]
  have := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [frobDense σ hσ] at this
  exact this (Subgroup.mem_top g)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem killed (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ r : ℕ, 0 < r ∧ ∀ x : M, (l : ℤ_[l]) ^ r • x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe12.killed l M

private theorem H0dual_eq {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have : coSub χ ρ ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, x, rfl⟩
      have := hf g x
      simp [this]
    exact fun w hw => this hw
  · intro hf g x
    have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this

private theorem card_co {G Q A V : Type} [Group G] [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup V]
    [Module A V] [Module Q V] [IsScalarTower Q A V] (hs : Function.Surjective (algebraMap Q A)) (χ : G →* Qˣ)
    (χ' : G →* Aˣ) (h : ∀ g, ((χ' g : Aˣ) : A) = algebraMap Q A (χ g : Qˣ))
    (ρ : Representation A G V) : Nat.card (V ⧸ coSub χ' ρ) = Nat.card (V ⧸ coSub χ (resCoef Q ρ)) := by
  have e : coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
    unfold coSub
    rw [Submodule.restrictScalars_span Q A hs]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, h, algebraMap_smul]
    rfl
  rw [e]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv Q (coSub χ' ρ)).toEquiv.symm

private def modRep (n : ℕ) {G Q V : Type} [Group G] [CommRing Q] [AddCommGroup V] [Module Q V] [Module (ZMod n) V]
    (ρ : Representation Q G V) : Representation (ZMod n) G V where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_level_of_finite_level_mod :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ), FinLevelMod l G χ d → FinLevel l G χ d := by
  intro l _ G _ _ χ d h M _ _ _ _ _ ρ hρ
  obtain ⟨r, hr, hk⟩ := killed l M
  have hk' : ∀ x : M, (l ^ r) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]; exact hk x
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule hk'⟩
  letI : Algebra ℤ_[l] (ZMod (l ^ r)) := (PadicInt.toZModPow r).toAlgebra
  have hs : Function.Surjective (algebraMap ℤ_[l] (ZMod (l ^ r))) := ZMod.ringHom_surjective _
  haveI : IsScalarTower ℤ_[l] (ZMod (l ^ r)) M := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    obtain ⟨k, hk2⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZModPow r a)
    have h0 : a - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hk2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
    obtain ⟨b, hb⟩ := h0
    change PadicInt.toZModPow r a • x = a • x
    rw [← hk2, Nat.cast_smul_eq_nsmul, eq_add_of_sub_eq hb.symm, add_smul, mul_smul, hk, smul_zero, zero_add,
      Nat.cast_smul_eq_nsmul]
  let ρ' : Representation (ZMod (l ^ r)) G M := modRep (l ^ r) ρ
  have e : resCoef ℤ_[l] ρ' = ρ := by ext; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := h r hr M ρ' hρ
  obtain ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, en⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ'
  rw [← e]
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm, Finite.of_equiv _ e2.toEquiv.symm, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨e'⟩ := en n
    have := a3 n hn
    exact e'.toEquiv.subsingleton
  · rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, a4]
  · rw [Nat.card_congr e2.toEquiv, a5, H0dual_eq,
      ← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator _).toEquiv]
    have : Finite (M ⧸ coSub ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ') :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    rw [KStar.Selmer.card_dual_of_baer KStar.Selmer.zmod_baer]
    exact card_co hs χ _ (fun g => rfl) ρ'
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private noncomputable def redMap {l : ℕ} [Fact l.Prime] {X Y : Type} [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y]
    [Module ℤ_[l] Y] (f : X →ₗ[ℤ_[l]] Y) (m : ℕ) : (X ⧸ lSub l X m) →ₗ[ℤ_[l]] (Y ⧸ lSub l Y m) :=
  Submodule.mapQ _ _ f fun x hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨f y, (map_smul _ _ _).symm⟩

private theorem card_quotient_eq_card_of_isReps (l : ℕ) [Fact l.Prime] (k : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ k}) = l ^ k := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hs : Function.Surjective (PadicInt.toZModPow (p := l) k) := fun z => by
    obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective z
    exact ⟨a, map_natCast _ a⟩
  rw [← PadicInt.ker_toZModPow, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv,
    Nat.card_zmod]

private theorem finite_padicInt_quot_span_of_ne_zero (l : ℕ) [Fact l.Prime] {q : ℤ_[l]} (hq : q ≠ 0) :
    Finite (ℤ_[l] ⧸ Ideal.span {q}) := by
  have h : Ideal.span {q} = Ideal.span {(l : ℤ_[l]) ^ q.valuation} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hq, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hq).symm
  rw [h]
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_eq_card_of_isReps]
  exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero

private theorem card_pi_padicInt_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ m}
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l] ⧸ I) :=
    LinearMap.pi (fun i => (Submodule.mkQ I) ∘ₗ LinearMap.proj i)
  have hsurj : Function.Surjective φ := by
    intro g
    choose y hy using fun i => Submodule.Quotient.mk_surjective I (g i)
    exact ⟨y, funext fun i => hy i⟩
  have hker : LinearMap.ker φ = lSub l (Fin n → ℤ_[l]) m := by
    ext x
    rw [LinearMap.mem_ker, mem_lSub]
    constructor
    · intro hx
      have h2 : ∀ i, ∃ y, (l : ℤ_[l]) ^ m * y = x i := fun i => by
        have h1 : (Submodule.Quotient.mk (x i) : ℤ_[l] ⧸ I) = 0 := congrFun hx i
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by rw [mul_comm]; exact ha⟩
      choose y hy using h2
      exact ⟨y, funext fun i => by simp [hy]⟩
    · rintro ⟨y, rfl⟩
      funext i
      show (Submodule.Quotient.mk _ : ℤ_[l] ⧸ I) = 0
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      exact ⟨y i, by simp [mul_comm]⟩
  rw [← hker, Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_fun,
    card_quotient_eq_card_of_isReps, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

theorem UpperTheory.card_quotient_powSubmodule_grows_finrank :
    ∀ (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [Module.Finite ℤ_[l] N], Grows l (fun m => Nat.card (N ⧸ lSub l N m)) (finrank ℤ_[l] N) := by
  intro l _ N _ _ _
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum ℤ_[l] N
  set D := DirectSum ι fun i => ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i with hD
  let g : N ≃ₗ[ℤ_[l]] (Fin n → ℤ_[l]) × D :=
    f.trans (LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ_[l] ℤ_[l] (Fin n))
      (LinearEquiv.refl _ _))
  haveI : Finite D := by
    haveI : ∀ i, Finite (ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i) := fun i =>
      finite_padicInt_quot_span_of_ne_zero l (pow_ne_zero _ (hp i).ne_zero)
    exact Finite.of_injective _ (DirectSum.linearEquivFunOnFintype ℤ_[l] ι _).injective
  have hrank : finrank ℤ_[l] N = n := by
    apply Module.finrank_eq_of_rank_eq
    have h0 : Module.rank ℤ_[l] D = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card D : ℤ_[l]), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      exact card_nsmul_eq_zero'
    rw [g.rank_eq, ← LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ_[l] (Fin n → ℤ_[l]) D),
      LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst,
      rank_range_of_injective _ LinearMap.inr_injective, h0, add_zero, rank_fun', Fintype.card_fin]
  rw [hrank]
  refine ⟨Nat.card D, fun m _ => ?_⟩
  let f1 : N →ₗ[ℤ_[l]] (Fin n → ℤ_[l]) := LinearMap.fst _ _ _ ∘ₗ g.toLinearMap
  let f2 : N →ₗ[ℤ_[l]] D := LinearMap.snd _ _ _ ∘ₗ g.toLinearMap
  let Ψ := LinearMap.prod (redMap f1 m) (redMap f2 m)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e1 : (Submodule.Quotient.mk (f1 x) : (Fin n → ℤ_[l]) ⧸ lSub l _ m) = 0 :=
      congrArg Prod.fst hq
    have e2 : (Submodule.Quotient.mk (f2 x) : D ⧸ lSub l D m) = 0 := congrArg Prod.snd hq
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub] at e1 e2
    obtain ⟨y1, hy1⟩ := e1
    obtain ⟨y2, hy2⟩ := e2
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub]
    refine ⟨g.symm (y1, y2), ?_⟩
    rw [← map_smul, Prod.smul_mk, hy1, hy2]
    simp [f1, f2]
  have hF := card_pi_padicInt_quot_lSub l n m
  haveI : Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  haveI : Finite (D ⧸ lSub l D m) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Finite (N ⧸ lSub l N m) := Finite.of_injective _ hinj
  have hsurj : Function.Surjective (redMap f1 m) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨Submodule.Quotient.mk (g.symm (y, 0)), ?_⟩
    simp [redMap, f1]
  constructor
  · rw [← hF]
    exact Nat.card_le_card_of_surjective _ hsurj
  · calc Nat.card (N ⧸ lSub l N m)
        ≤ Nat.card (((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) × (D ⧸ lSub l D m)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = l ^ (m * n) * Nat.card (D ⧸ lSub l D m) := by rw [Nat.card_prod, hF]
      _ ≤ l ^ (m * n) * Nat.card D :=
          Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ (Submodule.Quotient.mk_surjective _))
      _ ≤ l ^ (m * n) * l ^ (Nat.card D) :=
          Nat.mul_le_mul_left _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
      _ = l ^ (m * n + Nat.card D) := (pow_add _ _ _).symm
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.V.Loc.compKer :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (Pc : Cond O rbar) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), Represents Pc ρ → ∀ (x : R →ₐ[O] O) (P : Ideal R) {n : ℕ} (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ → (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C), OnComp Pc (ρ.map x).hom (ρ.map f) ↔ P ≤ RingHom.ker f := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar Pc R _ _ _ ρ hR x P n φ hc hy0 C _ _ _ f
  have hcomp : ∀ {A B D : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing B] [Algebra O B] [IsCO O B]
      [CommRing D] [Algebra O D] [IsCO O D] (u : A →ₐ[O] B) (v : B →ₐ[O] D) (r : Lift O rbar A),
      Lift.map v (Lift.map u r) = Lift.map (v.comp u) r := by
    intro A B D _ _ _ _ _ _ _ _ _ u v r
    apply Lift.ext
    ext γ a b
    rfl
  constructor
  · rintro ⟨B, _, _, _, _, ρB, hPB, ⟨x4, hx4⟩, y, hy⟩
    obtain ⟨g, hg, -⟩ := (hR B).2 ρB hPB
    subst hg
    have hf : y.comp g = f := by
      obtain ⟨h, -, huniq⟩ := (hR C).2 (Lift.map f ρ) ((hR C).1 f)
      rw [huniq (y.comp g) (by show Lift.map (y.comp g) ρ = _; rw [← hcomp]; exact hy), huniq f rfl]
    have hx : x4.comp g = x := by
      obtain ⟨h, -, huniq⟩ := (hR O).2 (Lift.map x ρ) ((hR O).1 x)
      refine (huniq (x4.comp g) ?_).trans (huniq x rfl).symm
      show Lift.map (x4.comp g) ρ = _
      rw [← hcomp]
      apply Lift.ext
      ext γ a b
      exact hx4 γ a b
    obtain ⟨y0, hy0ne, hann⟩ := hy0
    intro a ha
    rw [RingHom.mem_ker, ← hf]
    have hprod : g y0 * g a = 0 := by rw [← map_mul, hann a ha, map_zero]
    rcases mul_eq_zero.1 hprod with h0 | h0
    · exfalso
      apply hy0ne
      rw [← hx]
      simp [h0]
    · simp [h0]
  · intro hPf
    haveI : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
    have hker : RingHom.ker φ = P := hc.ker
    haveI hprime : P.IsPrime := hker ▸ RingHom.ker_isPrime φ
    have hxP : ∀ a ∈ P, x a = 0 := by
      intro a ha
      have h1 := hc.const a
      rw [← hker, RingHom.mem_ker] at ha
      rw [ha, map_zero] at h1
      exact (IsFractionRing.injective O E) (by rw [← h1, map_zero])
    have hfP : ∀ a ∈ P, f a = 0 := fun a ha => (RingHom.mem_ker).1 (hPf ha)
    letI hco : IsCO O (R ⧸ P) :=
      co_quot O R (R ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
    refine ⟨R ⧸ P, inferInstance, inferInstance, hco, inferInstance,
      Lift.map (Ideal.Quotient.mkₐ O P) ρ, (hR _).1 _, ⟨Ideal.Quotient.liftₐ P x hxP, ?_⟩,
      ⟨Ideal.Quotient.liftₐ P f hfP, ?_⟩⟩
    · intro γ a b
      rfl
    · rw [hcomp]
      apply Lift.ext
      ext γ a b
      rfl
end
