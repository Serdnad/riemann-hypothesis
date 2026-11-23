module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestriction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle367
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle293
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle328
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle371
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle372
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.tateDual_twistedSumSummand_isDeRham : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  first | exact @GlobalTheory.SummandDualDR.main | exact GlobalTheory.SummandDualDR.main | (intros; apply GlobalTheory.SummandDualDR.main <;> assumption)
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.potential_family_summand_restriction : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
      IsDR (Br.PD D.loc D.nbr i w hw) X.ρ ∧
      ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  first | exact @GlobalTheory.SummandDual.xdual | exact GlobalTheory.SummandDual.xdual | (intros; apply GlobalTheory.SummandDual.xdual <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.SmallActs

theorem toZModPow_cycZ_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (n : ℕ) (σ : G F Ω) (hσ : ∀ ζ : Ω, ζ ^ (l ^ n) = 1 → σ ζ = ζ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec : σ ζ = ζ ^ (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  rw [hσ ζ hζ.pow_eq_one] at hspec
  set m := (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val with hm
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ 1 := Units.ext (by simpa using hspec.symm)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])), ← hm,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 heq', Nat.cast_one]

theorem map_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (T : Matrix (Fin r) (Fin r) O)
    (h : ∀ a b, algebraMap O A ((T - 1) a b) = 0) : T.map (algebraMap O A) = 1 := by
  ext a b
  have := h a b
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem repOn_of_map_eq_one {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) (Y : Type) [AddCommGroup Y] [Module A Y] (g : Γ)
    (h : (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) = 1) (m : Fin r → Y) :
    repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m := by
  change (((κ g : Aˣ) : A) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A))) m = _
  rw [h, matAct_one]
  rfl

theorem small_acts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  intro D N X i s _ M L z hM hS A _ _ κ ρ hK hρ Y _ _ g hg
  have hT : ∀ g ∈ L, (Tmat i s g).map (algebraMap (X.O0 i) A) = 1 := fun g hg =>
    map_eq_one _ fun a b => hK _ (hS.2.2 g hg a b)
  have hc : PadicInt.toZModPow (nu X i + 1) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = 1 := by
    refine toZModPow_cycZ_eq_one (nu X i + 1) g fun ζ hζ => hS.2.1 g hg ζ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hM
    have e : 2 * X.l i ^ M = X.l i ^ (nu X i + 1) * (2 * X.l i ^ k) := by rw [hk, pow_add (X.l i) (nu X i + 1) k]; ring
    rw [e, pow_mul, hζ, one_pow]
  refine ⟨repOn_of_map_eq_one _ κ Y g (by rw [Tgl_coe]; exact hT g hg), repOn_of_map_eq_one _ κ Y g ?_, Units.ext hc⟩
  have hmem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
    have h1 : ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1 ∈
        RingHom.ker (PadicInt.toZModPow (nu X i + 1) : ℤ_[X.l i] →+* ZMod (X.l i ^ (nu X i + 1))) := by
      rw [RingHom.mem_ker, map_sub, hc, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, h1⟩ := h1
    change algebraMap (X.O0 i) A (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
    have h2 : algebraMap (X.O0 i) A ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i)) = 0 :=
      hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
    rw [sub_eq_iff_eq_add.1 h1, map_add (f := _), map_add (f := _), map_one, map_one, map_mul, map_pow, map_natCast, pow_succ, map_mul, h2,
      zero_mul, zero_add]
  have hinv : (Tmat i s g)⁻¹ = Tmat i s g⁻¹ := by
    rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]
  rw [hρ g, Tdual, hinv]
  ext a b
  have := congrFun (congrFun (hT g⁻¹ (L.inv_mem hg)) b) a
  rw [Matrix.map_apply] at this
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, he, one_mul, Matrix.transpose_apply, this,
    Matrix.one_apply, Matrix.one_apply]
  simp only [eq_comm]

end GlobalTheory.NewPrime.SmallActs

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

noncomputable section

namespace GlobalTheory.NewPrime

section
variable {A : Type} [CommRing A] {a r : ℕ}

theorem rect_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Z : Matrix (Fin r) (Fin a) A) (x : Fin a → B) : p.compLeft (Fin r) (rect Z x) = rect Z (p ∘ x) := by
  funext c

  simp [rect, map_sum]

theorem matAct_map {B B' : Type} [AddCommGroup B] [Module A B] [AddCommGroup B'] [Module A B'] (p : B →ₗ[A] B')
    (Φ : Matrix (Fin a) (Fin a) A) (x : Fin a → B) : p ∘ matAct Φ x = matAct Φ (p ∘ x) := by
  funext c

  simp [matAct, map_sum]

end

theorem comparison_cocycles : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (a a' : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (Φ' : Matrix (Fin a') (Fin a') A) Z Z' (γ σ : Bool → GE N), Univ bkP i s κ Q Φ Z → Univ bkP i s κ Q' Φ' Z' → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (γ b) = 0) → SelC bkP i s κ Y Q f) → (∀ (Y : Type) [AddCommGroup Y] [Module A Y] b m, repOn (Tgl i s) κ Y (σ b) m = m) → ∃ E : Matrix (Fin a) (Fin a') A, what₂ E ⊔ (what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) = ⊤ ∧ (∀ b, (Φ * E) b ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2)) ∧ ∀ j : Bool × Fin D.R.r, Z' (σ j.1) j.2 - Matrix.vecMul (Z (σ j.1) j.2) E ∈ what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) := by
  intro D N X bkP i s A _ _ κ Q Q' a a' Φ Φ' Z Z' γ σ hU hU' hSel hσ
  set W : Submodule A (Fin a' → A) := what₂ Φ' ⊔ what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) with hW
  letI tY : TopologicalSpace ((Fin a' → A) ⧸ W) := ⊥
  haveI : DiscreteTopology ((Fin a' → A) ⧸ W) := ⟨rfl⟩
  let gens : Fin a' → (Fin a' → A) ⧸ W := fun j => W.mkQ (Pi.single j 1)
  have hsum : ∀ v : Fin a' → A, ∑ j, v j • gens j = W.mkQ v := by
    intro v
    have : v = ∑ j, v j • (Pi.single j (1 : A) : Fin a' → A) := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [this]

    simp [gens, map_sum]
  have hrect : ∀ g c, rect (Z' g) gens c = W.mkQ (Z' g c) := fun g c => hsum _
  have hgens : matAct Φ' gens = 0 := by
    funext b
    have : matAct Φ' gens b = W.mkQ (Φ' b) := hsum (Φ' b)
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero W).2 ((le_sup_left : what₂ Φ' ≤ W) (Submodule.subset_span ⟨b, rfl⟩))
  have hf' := (hU' ((Fin a' → A) ⧸ W)).1 gens hgens
  have hγ : ∀ b, (fun g => rect (Z' g) gens) (γ b) = 0 := by
    intro b
    funext c
    show rect (Z' (γ b)) gens c = 0
    rw [hrect]
    exact (Submodule.Quotient.mk_eq_zero W).2
      ((le_sup_right : what₂ (fun j : Bool × Fin D.R.r => Z' (γ j.1) j.2) ≤ W) (Submodule.subset_span ⟨(b, c), rfl⟩))
  have hf := hSel _ _ hf' hγ
  obtain ⟨x, hx, m, hm⟩ := (hU ((Fin a' → A) ⧸ W)).2.2 _ hf
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin a) (Fin a') A, ∀ b, W.mkQ (E b) = x b :=
    ⟨fun b => (Submodule.mkQ_surjective W (x b)).choose, fun b => (Submodule.mkQ_surjective W (x b)).choose_spec⟩
  have hvm : ∀ v : Fin a → A, W.mkQ (∑ k, v k • E k) = ∑ k, v k • x k := fun v => by

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hE]
  refine ⟨E, ?_, ?_, ?_⟩
  · let S : Submodule A ((Fin a' → A) ⧸ W) := Submodule.span A (Set.range x)
    letI tS : TopologicalSpace (((Fin a' → A) ⧸ W) ⧸ S) := ⊥
    haveI : DiscreteTopology (((Fin a' → A) ⧸ W) ⧸ S) := ⟨rfl⟩
    have hpx : S.mkQ ∘ x = 0 := by
      funext b
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨b, rfl⟩)
    have hz : S.mkQ ∘ gens = 0 := by
      refine (hU' (((Fin a' → A) ⧸ W) ⧸ S)).2.1 _ ?_ ⟨S.mkQ.compLeft (Fin D.R.r) m, fun g => ?_⟩
      · rw [← matAct_map, hgens]
        funext b
        simp
      · have e := congrArg (S.mkQ.compLeft (Fin D.R.r)) (hm g)
        rw [map_sub, map_sub, rect_map, rect_map, hpx, repOn_map] at e
        have h0 : rect (Z g) (0 : Fin a → ((Fin a' → A) ⧸ W) ⧸ S) = 0 := by
          funext c
          simp [rect]
        rw [h0, sub_zero] at e
        exact e
    have hgS : ∀ j, gens j ∈ S := fun j =>
      (Submodule.Quotient.mk_eq_zero S).1 (congrFun hz j)
    rw [eq_top_iff]
    intro v _
    have hvS : W.mkQ v ∈ S := by
      rw [← hsum]
      exact S.sum_mem fun j _ => S.smul_mem _ (hgS j)
    have hSm : S = (what₂ E).map W.mkQ := by
      show Submodule.span A (Set.range x) = (Submodule.span A (Set.range E)).map W.mkQ
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨E b, ⟨b, rfl⟩, hE b⟩
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨b, (hE b).symm⟩
    rw [hSm] at hvS
    obtain ⟨e, he, hev⟩ := hvS
    have hd : v - e ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply, map_sub, hev, sub_self]
    have : v = e + (v - e) := by abel
    rw [this]
    exact Submodule.add_mem_sup he hd
  · intro b
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : (Φ * E) b = ∑ k, Φ b k • E k := by
      funext c
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [e1, hvm (Φ b)]
    exact congrFun hx b
  · rintro ⟨b, c⟩
    rw [← Submodule.Quotient.mk_eq_zero W, ← Submodule.mkQ_apply]
    have e1 : Matrix.vecMul (Z (σ b) c) E = ∑ k, Z (σ b) c k • E k := by
      funext t
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    have e2 := congrFun (hm (σ b)) c
    rw [hσ, sub_self] at e2
    show W.mkQ (Z' (σ b) c - Matrix.vecMul (Z (σ b) c) E) = 0
    rw [map_sub, e1, hvm (Z (σ b) c), ← hrect]
    exact e2

end GlobalTheory.NewPrime
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem setup_of_factor : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (M : ℕ) (ι : Type) [Fintype ι] (P : ι → PlE D.host) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ Q : Finset (PlE D.host)), SlopeTestRemainingChoices X i M A₀ P d → IsQ P Q → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → (∀ g, (∀ q, d q g = 1) → κ g = 1) → Setup bkP i s κ Q ∧ AntiHom X.cc κ ∧ ∀ z, IsTameInertiaElementAtTwistPrime X i z → κ z = 1 := by
  intro D N X bkP i s hG M ι _ P d A₀ Q hA hQ A _ _ _ _ κ _ h1
  have hfin : Module.Finite (X.O0 i) A := Module.Finite.of_finite
  refine ⟨⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv B hB σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv B hB σ hσ => h1 σ fun q => ?_⟩, fun g g' hg => ?_, ?_⟩
  · by_contra hn
    have h : IsLocalRing.maximalIdeal (X.O0 i) ≤ (IsLocalRing.maximalIdeal A).comap (algebraMap (X.O0 i) A) :=
      (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
        Algebra.IsIntegral.isIntegral (IsLocalRing.maximalIdeal A))).ge
    exact h hn hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · rw [← map_pow]
    refine h1 _ fun q => ?_
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, toAdd_one]
  · exact (hA.2.2 q).2.2.1 v hv B hB σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) B hB σ hσ
  · rw [eq_inv_iff_mul_eq_one, ← map_mul]
    refine h1 _ fun q => ?_
    rw [map_mul, (hA.2.2 q).2.1 g g' hg, inv_mul_cancel]
  · rintro z ⟨v, hv, B, hB, hz, -⟩
    exact h1 z fun q => (hA.2.2 q).2.2.2.1 v (fun hq => (hA.1 q v hq).2.2.2.1 (X.primes_subset_exceptional i hv)) B hB z hz

end GlobalTheory.NewPrime
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LamHom

def chr {B ι : Type} [CommRing B] [Fintype ι] {n : ℕ} [NeZero n] (u : ι → B) (hu : ∀ q, u q ^ n = 1) :
    Multiplicative (ι → ZMod n) →* B := GlobalTheory.RootCharacter.rootChar u hu

theorem chr_single {B ι : Type} [CommRing B] [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (hn : 1 < n) (u : ι → B)
    (hu : ∀ q, u q ^ n = 1) (q : ι) : chr u hu (Multiplicative.ofAdd (Pi.single q 1)) = u q := by
  haveI : Fact (1 < n) := ⟨hn⟩
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod n) : ι → ZMod n) p).val = u q
  rw [Finset.prod_eq_single q]
  · simp [ZMod.val_one]
  · intro p _ hp
    simp [Pi.single_eq_of_ne hp]
  · simp

theorem exists_lamHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (B : Type) [CommRing B] [Algebra (X.O0 i) B] (ξ : ι → B), 0 < nu X i → nu X i + 1 ≤ M → Kills i B → (∀ q, ξ q ^ X.l i ^ (M - nu X i - 1) = 0) → ∃ φ : abelian₂ X i M ι →ₐ[X.O0 i] B, (∀ F, φ (toLam X i M ι F) = MvPolynomial.aeval ξ F) ∧ ∀ d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))), ∃ κ : GE N →* Bˣ, (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) ∧ IsChar i κ ξ d := by
  intro D N X i M ι _ B _ _ ξ _ hM hK hξ
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hm : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have h4 : ((X.l i : ℕ) : B) ^ (nu X i + 1) = 0 := by
    have h := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hm)
    rw [map_mul, map_pow, map_natCast] at h
    rw [pow_succ]
    exact h
  have hn : 1 < X.l i ^ M := Nat.one_lt_pow (by omega) hp.one_lt
  haveI : NeZero (X.l i ^ M) := ⟨by omega⟩
  have hu : ∀ q, (1 + ξ q) ^ (X.l i ^ M) = 1 := fun q =>
    KStar.Tree.one_add_pow_prime_pow_eq_one hp h4 hM (hξ q)
  let φ : abelian₂ X i M ι →ₐ[X.O0 i] B := MonoidAlgebra.lift (X.O0 i) B (Del X i M ι) (chr (fun q => 1 + ξ q) hu)
  have hφ : ∀ x, φ (MonoidAlgebra.of (X.O0 i) (Del X i M ι) x) = chr (fun q => 1 + ξ q) hu x := fun x =>
    MonoidAlgebra.lift_of _ x
  refine ⟨φ, fun F => ?_, fun d => ⟨(Units.map (φ : abelian₂ X i M ι →* B)).comp (delInv i M d), fun g => rfl, fun g => ?_⟩⟩
  · have : φ.comp (toLam X i M ι) = MvPolynomial.aeval ξ := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_one, hφ]
      have := chr_single hn (fun q => 1 + ξ q) hu q
      rw [sub_eq_iff_eq_add']
      convert this
    exact DFunLike.congr_fun this F
  · have h1 : ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) *
        MonoidAlgebra.of (X.O0 i) (Del X i M ι) (delAll X i M d g) = 1 :=
      Units.inv_mul ((MonoidAlgebra.of (X.O0 i) (Del X i M ι)).toHomUnits (delAll X i M d g))
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφ] at h2
    exact h2

end GlobalTheory.NewPrime.LamHom
end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime


open IsLocalRing GlobalTheory.ScalarFrob in
theorem noInvDual_of_setup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ z hS hρ hz Y' _ _ m hm
  obtain ⟨h, hloc, -, -, hκ, -⟩ := hS
  obtain ⟨e, he, -, hu, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have e1 : resT i s z = residue (X.O0 i) e • 1 := by
    rw [resT_apply, he]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  have e2 := dual_of_scalar i s (by rw [hε]; simp) c0 e1
  rw [← hρ z] at e2
  have hκ' : ∃ n : ℕ, κ⁻¹ z ^ (X.l i ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hκ z
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  exact eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ hκ' (inv_ne_one.2 c1) e2 (q := 1) Nat.cast_one m
    (by rw [one_smul]; exact hm z)

end GlobalTheory.NewPrime
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Generic

variable {A R : Type} [CommRing A] [CommRing R] {ι : A →+* R} {p : ℕ} {t : R}

theorem Near.map_of_fixed (g : R →+* R) (hg : ∀ a, ∃ b, ι b = g (ι a)) (ht : g t = t) {m : ℕ}
    {x : R} (hx : Near ι p t m x) : Near ι p t m (g x) := by
  obtain ⟨a, r, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hg a
  exact ⟨b, g r, by rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, ht, hb]⟩

theorem fixed_complete_generic {G : Type} (H : Set G) (act : G → (R →+* R)) (S : Subring R)
    (hS : ∀ x, x ∈ S ↔ ∀ g ∈ H, act g x = x) {τ : A} (hτ : ι τ = t)
    (hg : ∀ g a, ∃ b, ι b = act g (ι a))
    (hsep : ∀ x : R, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (hcomp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, Near ι p t (i + k) (f i)) →
      ∃ x, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hlift : ∀ x : R, (∀ g ∈ H, ∃ r, act g x - x = (p : R) * r) →
      ∃ y ∈ S, ∃ r, y - x = (p : R) * r)
    (ht : t ∈ S) (k : ℕ) (f : ℕ → R) (hf : ∀ i, f i ∈ S) (hn : ∀ i, Near ι p t (i + k) (f i)) :
    ∃ x ∈ S, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  obtain ⟨x, hx⟩ := hcomp k f hn
  obtain ⟨y, hy, r, hr⟩ := hlift x fun g hgH => hsep _ fun m => by
    have h1 : act g (∑ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, f i :=
      (hS _).1 (S.sum_mem fun i _ => hf i) g hgH
    have h2 := (Near.map_of_fixed (act g) (hg g) ((hS _).1 ht g hgH) (hx m)).sub (hx m)
    rw [map_sub, h1, sub_sub_sub_cancel_right] at h2
    exact h2.mono hτ (Nat.le_add_right m k)
  refine ⟨y, hy, fun m => ?_⟩
  have h3 := (Near.of_mul (ι := ι) (p := p) (t := t) (m + k) r).add (hx m)
  rw [← hr, sub_add_sub_cancel] at h3
  exact h3

end Generic

theorem fixSub_nearPi_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (H : Set (GQ l)), piR AI LL s ∈ fixSub AI LL H → ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, f i ∈ fixSub AI LL H) → (∀ i, NearPi AI LL s (i + k) (f i)) → ∃ x ∈ fixSub AI LL H, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  intro l _ P AI LL s H
  exact fixed_complete_generic H (fun g => (AI.gRW LL g : RW LL →+* RW LL)) (fixSub AI LL H)
    (fun _ => mem_fixSub) (τ := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) rfl
    (fun g a => ⟨GlobalTheory.Cyc.Decomp.gRA AI LL g a, GlobalTheory.Cyc.Decomp.inclR_gRA AI LL g a⟩)
    (GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s).1 (GlobalTheory.T.nearPi_sep_complete_alt l P AI LL s).2 (GlobalTheory.T.exists_galois_fixed_lift_of_fixed_mod_prime l P AI LL H)

end GlobalTheory.Decompl
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_irreducible_detTwist_of_stdTrace_twoBlock : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 → ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  first | exact @GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero | exact GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero | (intros; apply GlobalTheory.LevelType.RestrictionTwo.exists_irr_hc_of_stdTrace_ne_zero <;> assumption)
end
