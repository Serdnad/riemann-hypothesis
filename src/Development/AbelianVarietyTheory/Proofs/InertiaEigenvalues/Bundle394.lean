module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle373
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle380
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle375
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocalPair

theorem exists_dual_equiv {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap n)) (fun y y' => by refine DFunLike.ext _ _ fun x => ?_; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual (ZMod n) M') = Nat.card M' := GlobalTheory.ZModDual.card_dual_eq n M'
  have : Finite (Module.Dual (ZMod n) M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (fun x => ((P x).toZModLinearMap n : Module.Dual (ZMod n) M')) ?_
    intro x x' hx
    rw [← sub_eq_zero]
    refine h1 _ fun y => ?_
    rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
    exact DFunLike.congr_fun hx y
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem dual_equivariant {n : ℕ} {Λ D : Type} [CommRing Λ] [Group D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Module Λ M] {M' : Type} [AddCommGroup M'] [Module Λ M']
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n) (χ : D →* (ZMod n)ˣ)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = (χ g : ZMod n) * P x y) (e : M' ≃+ TDual (ZMod n) M)
    (he : ∀ y x, e y x = P x y) (g : D) (y : M') : e (ρ' g y) = twDual χ (zmodRep n ρ) g (e y) := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [twDual_apply, he, he]
  change _ = _ * P (ρ g⁻¹ x) y
  rw [← hP, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

private def cocycleTransport : Z1 ρ ≃+ Z1 ρ' where
  toFun z := ⟨fun g => e (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  invFun z := ⟨fun g => e.symm (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    apply e.injective
    rw [map_add (f := _), he]
    simp only [AddEquiv.apply_symm_apply]
    exact z.2.2 g h⟩
  left_inv z := Subtype.ext (funext fun g => e.symm_apply_apply _)
  right_inv z := Subtype.ext (funext fun g => e.apply_symm_apply _)
  map_add' z w := Subtype.ext (funext fun g => map_add e _ _)


include he in
private theorem exists_H1_transport : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleTransport ρ ρ' e he) ?_, fun z z' h => ?_⟩
  · ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
      refine (mem_coboundaries1 ρ' _).2 ⟨e m, fun g => ?_⟩
      change e (z.1 g) = _
      rw [← he, ← map_sub]
      exact congrArg e (hm g)
    · intro hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hz
      refine ⟨(cocycleTransport ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleTransport ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleTransport ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

private theorem card_H0_transport {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem local_pair : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  intro hLF hLD hLE F Ω _ _ _ _ _ l _ n A v hA Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let χ := (cycMod F Ω l n).comp (Dec (F := F) A).subtype
  refine ⟨fun y => ⟨fun H => ?_, ?_⟩, fun hv => ?_⟩
  · obtain ⟨e, he⟩ := exists_dual_equiv P.flip h2 h1
    have hee := dual_equivariant ρ' ρ P.flip χ (fun g y x => hP g x y) e he
    have hinj := (hLD F Ω l n W' A (zmodRep (l ^ n) ρ') v hn hA hρ').2.2.2.1.1
    rw [injective_iff_map_eq_zero] at hinj
    let y' : Z1 ((zmodRep (l ^ n) ρ').comp (MonoidHom.id _)) := ⟨y.1, y.2.1, y.2.2⟩
    have h0 := hinj (Submodule.Quotient.mk y') (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨x, rfl⟩ := (cocycleTransport ρ ((twDual χ (zmodRep (l ^ n) ρ')).comp (MonoidHom.id _)) e hee).surjective x
      obtain ⟨f, hf1, hf2⟩ := H x
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨f, hf1.continuous, funext fun p => ?_⟩)
      exact (hf2 p.1 p.2).symm.trans (he _ _).symm)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩ x
    refine ⟨fun g => -P (x.1 g) (ρ' g m), (IsLocallyConstant.iff_continuous _).2 ?_, fun g h => ?_⟩
    · exact ((continuous_of_discreteTopology (f := fun p : W × W' => P p.1 p.2)).comp
        (x.2.1.prodMk (hρ'.comp (continuous_id.prodMk continuous_const)))).neg
    · beta_reduce
      rw [mul_neg, ← hP, x.2.2, hm, map_mul, Module.End.mul_apply]
      simp only [map_add (f := _), map_sub, AddMonoidHom.add_apply]
      ring
  · obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2
    have hee := dual_equivariant ρ ρ' P χ hP e he
    obtain ⟨⟨j⟩, -, -, -, hb⟩ := hLD F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ
    have hE := (hLE F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ).2 hv
    obtain ⟨T, -⟩ := exists_H1_transport ρ (zmodRep (l ^ n) ρ) (AddEquiv.refl W) fun _ _ => rfl
    have c0 := card_H0_transport ρ (zmodRep (l ^ n) ρ) id Function.surjective_id (AddEquiv.refl W) fun _ _ => rfl
    have c0' := card_H0_transport ρ' ((twDual χ (zmodRep (l ^ n) ρ)).comp (MonoidHom.id _)) id Function.surjective_id e hee
    have : Finite (TDual (ZMod (l ^ n)) W) := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr T.toEquiv, hE, c0, ← c0']
    congr 1
    refine (Nat.card_eq_of_bijective _ hb).trans ?_
    exact (Nat.card_congr (LinearEquiv.congrRight j).toEquiv).trans (GlobalTheory.ZModDual.card_dual_eq _ _)

end GlobalTheory.LocalPair
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LocInv

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [(Submodule.mem_bot _).1 hx, zero_smul]

theorem dual_eq_one {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ)
    (v : PlE D.host) (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (σ : GE N)
    (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) : ρ σ = 1 := by
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hl
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hvl (N.plOm.2 v) (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  have h2 : eps0 X i σ = 1 := by
    rw [eps0, MonoidHom.comp_apply, h1, map_one]
  have h3 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s h v hl hS _ (N.plOm.2 v) σ hσ
  apply Units.ext
  rw [hρ σ, Tdual, h2, ← Tgl_coe, h3]
  simp

theorem local_invariants_killed : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  intro _ D N X bkP i s _ M R n d A₀ L z P hM hz hL hSt A _ _ _ _ κ Q ρ t a hQ hSet _ hρ hch ha Y _ _ _ _ v hv m hm
  obtain ⟨hG, hloc, -, hκo, hκl, -, hQl, -⟩ := hSet
  have hκl' : ∀ g, ∃ k : ℕ, κ⁻¹ g ^ (X.l i ^ k) = 1 := fun g => by
    obtain ⟨k, hk⟩ := hκl g
    exact ⟨k, by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]⟩
  by_cases hS : v ∈ Spl i
  · have hker : (κ⁻¹).ker = κ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h0 := (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hG v hS A κ⁻¹ (hker ▸ hκo) hκl' Y
      (tors_of_finite A Y) ρ (Or.inr hρ)).1
    have : m ∈ H0 ((repOn ρ κ⁻¹ Y).comp (DecV N v).subtype) := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => hm g.1 g.2
    rw [h0, Submodule.mem_bot] at this
    rw [this, smul_zero]
  have hvQ : v ∈ Q := hv.resolve_left hS
  obtain ⟨q, hq⟩ := (hQ v).1 hvQ
  rcases q with b | q
  · have hA : ∀ w, Over (P (.inl b)) w → w ∉ X.S0 i ∧ normV w % X.l i = 1 := fun w hw => by
      obtain ⟨-, -, -, h0, -, hn⟩ := hSt.1.1 _ w hw
      exact ⟨h0, mod_l_eq_one i hM hn⟩
    have hp := hA v hq
    have hn := GlobalTheory.ScalarFrob.natCast_eq_one_of_mod i hp.2
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    obtain ⟨c, c0, c1, hc⟩ := GlobalTheory.ScalarFrob.frob_scalar_place i s bkP hG hz hL.1 hA (hSt.2.1 b).2 hq hσ
    have hc' : ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) =
        c⁻¹ • 1 := by
      rw [hρ, GlobalTheory.ScalarFrob.dual_of_scalar i s (GlobalTheory.ScalarFrob.eps_frob i hp.1 hn hσ) c0 hc]
    rw [GlobalTheory.ScalarFrob.eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ (hκl' σ) (inv_ne_one.2 c1) hc'
      (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm σ hσ.1), smul_zero]
  · obtain ⟨γ, hγ, hd⟩ := (hSt.1.2.2 (.inr q)).2.2.2.2 v hq _ (N.plOm.2 v) (Multiplicative.ofAdd 1)
    have hρ1 := dual_eq_one bkP i s hG.1 hρ v (hQl v hvQ) hS γ hγ
    have hk := hch γ
    haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (Fact.out : (X.l i).Prime).one_lt⟩
    rw [Finset.prod_eq_single (Sum.inr q)] at hk
    · have hd' : d (P (.inr q)) γ = Multiplicative.ofAdd 1 := hd
      simp only [hd', toAdd_ofAdd, ZMod.val_one, pow_one] at hk
      have hinv : ((κ⁻¹ γ : Aˣ) : A) = 1 + a (.inr q) * t := by
        rw [MonoidHom.inv_apply]
        exact Units.inv_eq_of_mul_eq_one_right hk
      have e := hm γ (Ine_le_Dec _ hγ)
      have e2 : repOn ρ κ⁻¹ Y γ m = (1 + a (.inr q) * t) • m := by
        simp [repOn, hρ1, matAct_one, ← hinv]
      rw [e2, add_smul, one_smul, add_eq_left, mul_smul] at e
      exact ((ha q).smul_eq_zero).1 e
    · intro q' _ hne
      have hn : ¬ Over (P q') v := fun h' => hne (hSt.1.2.1 _ _ (over_trans h' (over_symm hq)))
      have : d (P q') γ = 1 := (hSt.1.2.2 q').2.2.2.1 v hn _ (N.plOm.2 v) γ hγ
      simp [this]
    · simp

end GlobalTheory.NewPrime.LocInv
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.Combine

variable {O V ι Γ Q G C : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup Q] [Module O Q]

def blk (act : ι → Γ → V → V) {a : ℕ} (x : Fin a → ι) (γ : Γ) (v : Fin a → V) : Fin a → V :=
  fun b => act (x b) γ (v b)

def appL (a₁ a₂ : ℕ) : ((Fin a₁ → V) × (Fin a₂ → V)) →ₗ[O] (Fin (a₁ + a₂) → V) where
  toFun p := Fin.append p.1 p.2
  map_add' p q := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  map_smul' c p := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def resL₁ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₁ → V) where
  toFun v := fun j => v (Fin.castAdd a₂ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def resL₂ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₂ → V) where
  toFun v := fun j => v (Fin.natAdd a₁ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resL₁_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₁ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₁ := by
  funext j; simp [resL₁]

theorem resL₂_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₂ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₂ := by
  funext j; simp [resL₂]

theorem blk_append (act : ι → Γ → V → V) {a₁ a₂ : ℕ} (x₁ : Fin a₁ → ι) (x₂ : Fin a₂ → ι) (γ : Γ)
    (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    blk act (Fin.append x₁ x₂) γ (Fin.append v₁ v₂) = Fin.append (blk act x₁ γ v₁) (blk act x₂ γ v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [blk]

theorem append_sub {a₁ a₂ : ℕ} (u₁ v₁ : Fin a₁ → V) (u₂ v₂ : Fin a₂ → V) :
    Fin.append u₁ u₂ - Fin.append v₁ v₂ = Fin.append (u₁ - v₁) (u₂ - v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def HasPres (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C) (S : Set (G → C)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ι) (E : Fin a → V) (Y : Submodule O (Fin a → V)), Y.FG ∧
    ∃ (hst : ∀ γ : Γ, ∀ y ∈ Y, blk act x γ y ∈ Y) (hE : ∀ γ : Γ, blk act x γ E - E ∈ Y),
      ∀ c ∈ S, ∃ φ : ↥Y →ₗ[O] Q, (∀ (γ : Γ) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = W γ (φ y)) ∧
        c = fun g => out (φ ⟨_, hE (gl g)⟩)

variable (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C)

theorem hasPres_empty : HasPres (O := O) act W gl out ∅ := by
  refine ⟨0, Fin.elim0, 0, ⊥, Submodule.fg_bot, ?_, ?_, ?_⟩
  · intro γ y _
    rw [Subsingleton.elim (blk act Fin.elim0 γ y) 0]; exact Submodule.zero_mem _
  · intro γ
    rw [Subsingleton.elim (blk act Fin.elim0 γ 0 - 0) 0]; exact Submodule.zero_mem _
  · intro c hc; exact absurd hc (Set.notMem_empty c)

theorem hasPres_union {S T : Set (G → C)} (hS : HasPres (O := O) act W gl out S)
    (hT : HasPres (O := O) act W gl out T) : HasPres (O := O) act W gl out (S ∪ T) := by
  obtain ⟨a₁, x₁, E₁, Y₁, hY₁, hst₁, hE₁, hφ₁⟩ := hS
  obtain ⟨a₂, x₂, E₂, Y₂, hY₂, hst₂, hE₂, hφ₂⟩ := hT
  set Y : Submodule O (Fin (a₁ + a₂) → V) := (Y₁.prod Y₂).map (appL a₁ a₂) with hYdef
  have mem_of : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, Fin.append y₁ y₂ ∈ Y := fun y₁ h₁ y₂ h₂ =>
    Submodule.mem_map_of_mem (f := appL a₁ a₂) (p := Y₁.prod Y₂) (r := (y₁, y₂)) (Submodule.mem_prod.2 ⟨h₁, h₂⟩)
  have mem_iff : ∀ y ∈ Y, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, y = Fin.append y₁ y₂ := by
    intro y hy
    obtain ⟨⟨y₁, y₂⟩, ⟨h₁, h₂⟩, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨y₁, h₁, y₂, h₂, rfl⟩
  have r₁ : ∀ y ∈ Y, resL₁ (O := O) a₁ a₂ y ∈ Y₁ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₁_append]; exact h₁
  have r₂ : ∀ y ∈ Y, resL₂ (O := O) a₁ a₂ y ∈ Y₂ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₂_append]; exact h₂
  have hst : ∀ γ : Γ, ∀ y ∈ Y, blk act (Fin.append x₁ x₂) γ y ∈ Y := by
    intro γ y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [blk_append]
    exact mem_of _ (hst₁ γ y₁ h₁) _ (hst₂ γ y₂ h₂)
  have hEq : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ =
      Fin.append (blk act x₁ γ E₁ - E₁) (blk act x₂ γ E₂ - E₂) := by
    intro γ; rw [blk_append, append_sub]
  have hE : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ ∈ Y := by
    intro γ; rw [hEq]; exact mem_of _ (hE₁ γ) _ (hE₂ γ)
  refine ⟨a₁ + a₂, Fin.append x₁ x₂, Fin.append E₁ E₂, Y, ?_, hst, hE, ?_⟩
  · exact (hY₁.prod hY₂).map _
  · intro c hc
    rcases hc with hc | hc
    · obtain ⟨φ, hφ, rfl⟩ := hφ₁ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₁ := ((resL₁ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₁ (fun y => r₁ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₁) = ⟨_, hst₁ γ y₁ h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₁_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₁) = ⟨y₁, h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₁_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₁, h₁⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₁_append]
    · obtain ⟨φ, hφ, rfl⟩ := hφ₂ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₂ := ((resL₂ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₂ (fun y => r₂ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₂) = ⟨_, hst₂ γ y₂ h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₂_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₂) = ⟨y₂, h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₂_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₂, h₂⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₂_append]

theorem hasPres_finset (F : Finset (G → C)) (h : ∀ c ∈ F, HasPres (O := O) act W gl out {c}) :
    HasPres (O := O) act W gl out (F : Set (G → C)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hasPres_empty (O := O) act W gl out
  | insert c F hc ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    exact hasPres_union act W gl out (h c (Finset.mem_insert_self c F))
      (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

end GlobalTheory.Pass.LocDual.OneX.Combine

end

namespace GlobalTheory.Pass.LocDual.OneX


open GlobalTheory.Pass.LocDual.OneX.Combine in


theorem cutCoc_finset_common : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
    (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆
    cutCoc i w hw r Xs M →
    ∃ (a : ℕ) (x : Fin a → ↥Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG ∧
    ∃ (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y),
    ∀ c ∈ F, ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
    (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
    c = fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs k M F hF
  have h := hasPres_finset (O := D.nd.O i)
    (fun (x : ↥Xs) (γ : GE D.nd) (v : Fin D.R.nV → KK D.nd i) => (mapM (toK D.nd i) (rTwO D.nd i r x) γ).mulVec v)
    (fun γ q => WKG M γ q) (gl i w hw) (Br.phi (D.nbr i w hw) k) F ?_
  · exact h
  · intro c hc
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, φ, hφ, rfl⟩ := hF (Finset.mem_coe.2 hc)
    refine ⟨a, fun j => ⟨x j, hx j⟩, E, Y, hY, hst, hE, ?_⟩
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    exact ⟨φ, hφ, rfl⟩

end GlobalTheory.Pass.LocDual.OneX
end

section


theorem _root_.GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  first | exact @GlobalTheory.bhattScholze_coeff | exact GlobalTheory.bhattScholze_coeff | (intros; apply GlobalTheory.bhattScholze_coeff <;> assumption)
end
