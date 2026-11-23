module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle001
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut
namespace UpperTheory.V.Pr
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
section Ord
variable (l : ℕ) {O : Type} [CommRing O] [IsLocalRing O] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω)
  (B : ValuationSubring Ω)
end Ord
variable {l : ℕ} [Fact l.Prime] (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω)
def AutEnd3Alt (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A]
    (r : G ℚ Ω →* GG (m := 3) (R := A)),
    OrdPt l η Ψ σ g₁ B r →
    (∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ η.ker → MatIrr U (mats (UnitaryThreeInertia.push A.val r))) →
    ∀ [Algebra K Ω] (ρ : G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ s, (ρ s).val = (UnitaryThreeInertia.push A.val r (Base.galEmb ℚ K Ω s)).mat) →
      _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw ρ (cycBar K Ω l)⁻¹)
def HostEndAlt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], IsQi K →
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ ∧
    FinEnd l (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B ∧
    _root_.UpperTheory.V.Pr.AutEnd3Alt c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B K ι
def GdEndAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ)
    (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
  ∃ g₁, Marks D.η D.Ψ D.cc g₁ ∧ FinEnd l D.η D.Ψ D.cc g₁ B ∧ _root_.UpperTheory.V.Pr.AutEnd3Alt c D.η D.Ψ D.cc g₁ B K ι ∧
    _root_.UpperTheory.V.Z.Win.Dn.AutEnd2Ao c D.η D.Ψ D.cc g₁ B e ι
end UpperTheory.V.Pr
end
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp)
namespace UpperTheory.V.Z.Sym
structure AdInAlt {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : _root_.Formalism.ConjugateSelfDual.G L Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous r
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
  irr : IrrOpen r
  gap : 2 ≤ m
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, r s = 1
  away : ∃ τ : Fin 2 → _root_.Formalism.ConjugateSelfDual.G L Ω →* (Qbar l)ˣ, (∀ i, Continuous (τ i)) ∧ TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (_root_.ReciprocityTheory.Gal.Dec (F := L) A) κ ∧
      ∀ s : ↥(_root_.ReciprocityTheory.Gal.Dec (F := L) A), (s : _root_.Formalism.ConjugateSelfDual.G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k
def UnitaryThreeAutomorphyDense : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (N w : ℕ) (χ' η θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → χ' ≠ η → ∀ M : ℕ, M ≠ 0 → 2 * l ∣ M → UnrSplit L M →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1) →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ r : _root_.Formalism.ConjugateSelfDual.G L Ω →* GL (Fin 3) (Qbar l), IrrOpen r ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', 1, (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', 1, χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), 0, -(m : ℤ)] (cycBar L Ω l)⁻¹ r
end UpperTheory.V.Z.Sym
end
end
end

section




section
section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi
private theorem ae_abs {A R P Lev B ι : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty Lev] [Group B]
    (MK : Lev → Submodule A P) (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A B S) (κ : Lev → Subgroup B)
    (hfix : ∀ K, (fixd ρ (κ K)).map S.subtype = MK K) (hex : ∀ f : S, ∃ K, (f : P) ∈ MK K)
    (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K') (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K)
    (hop : ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z))
    (μ : ∀ K, R →+* Module.End A (MK K))
    (hμ : ∀ K K' (φ : MK K →ₗ[A] MK K'), Function.Injective φ →
      (∀ i (y y' : MK K), (y' : P) = op i y → (φ y' : P) = op i (φ y)) → ∀ t y, φ (μ K t y) = μ K' t (φ y)) :
    ∃ α : R →+* Module.End A S, (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := by
  have hle : ∀ K, MK K ≤ S := fun K => by
    rw [← hfix]
    exact Submodule.map_subtype_le _ _
  have hmem : ∀ K (z : S), (z : P) ∈ MK K ↔ z ∈ fixd ρ (κ K) := fun K z => by
    rw [← hfix]
    exact ⟨fun ⟨y, hy, e⟩ => Subtype.ext e ▸ hy, fun h => ⟨z, h, rfl⟩⟩
  let e : ∀ K, (MK K).comap S.subtype ≃ₗ[A] MK K := fun K => Submodule.comapSubtypeEquivOfLe (hle K)
  have he : ∀ K y, (e K y : P) = (y : S) := fun _ _ => rfl
  have he' : ∀ K y, (((e K).symm y : S) : P) = y := fun K y => by rw [← he, LinearEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := levelUR2Glue A R S Lev (fun K => (MK K).comap S.subtype)
    (fun K => (e K).symm.conjRingEquiv.toRingHom.comp (μ K)) hex
    (fun K K' => by
      obtain ⟨K'', h1, h2⟩ := hinf K K'
      exact ⟨K'', fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h1 hk),
        fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h2 hk)⟩)
    (fun K K' h t y => by
      have h' : MK K ≤ MK K' := fun x hx => h (x := ⟨x, hle K hx⟩) hx
      have := hμ K K' (Submodule.inclusion h') (Submodule.inclusion_injective h') (fun i y y' hy => hy) t (e K y)
      refine Subtype.ext ?_
      exact (he' K' _).trans ((congrArg Subtype.val this).symm.trans (he' K _).symm))
  have h2 : ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := fun K t y z hz => by
    have hy : y = e K ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩ := Subtype.ext hz.symm
    rw [hy]
    exact (congrArg Subtype.val (hα K t ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩)).trans (he' K _)
  refine ⟨α, fun t g z => ?_, h2⟩
  obtain ⟨K, hK⟩ := hex z
  obtain ⟨K', hK'⟩ := hconj K g
  let φ : MK K →ₗ[A] MK K' := (S.subtype ∘ₗ ρ g ∘ₗ Submodule.inclusion (hle K)).codRestrict _ fun y =>
    (hmem K' _).2 fun k hk => by
      have := (hmem K (Submodule.inclusion (hle K) y)).1 y.2 _ (hK' k hk)
      change ρ k (ρ g _) = ρ g _
      conv_rhs => rw [← this]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left]
  have hφ : ∀ y, (φ y : P) = ρ g (Submodule.inclusion (hle K) y) := fun _ => rfl
  have hinj : Function.Injective φ := fun y y' h => by
    have h3 : ρ g (Submodule.inclusion (hle K) y) = ρ g (Submodule.inclusion (hle K) y') :=
      Subtype.ext (by rw [← hφ, ← hφ, h])
    have h4 := congrArg (ρ g⁻¹) h3
    simp only [Representation.inv_self_apply] at h4
    exact Submodule.inclusion_injective _ h4
  have h5 := hμ K K' φ hinj (fun i y y' hy => hop g i _ _ hy) t ⟨z, hK⟩
  refine Subtype.ext ?_
  rw [h2 K' t (φ ⟨z, hK⟩) (ρ g z) rfl, ← h5, hφ]
  exact congrArg (fun x => (ρ g x : P)) (Subtype.ext (h2 K t ⟨z, hK⟩ z rfl).symm)
private theorem ae_ind {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] (p : (∀ q, G q) → Prop)
    (h1 : p 1) (hm : ∀ g g', p g → p g' → p (g * g')) (hs : ∀ q g, p (Pi.mulSingle q g)) (g : ∀ q, G q) : p g := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun q _ => hs q _
private theorem ae_gen {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] {A P ι : Type} [CommRing A]
    [AddCommGroup P] [Module A P] (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A (∀ q, G q) S)
    (s : ∀ q, G q → Module.End A P) (hρ : ∀ q g f, (ρ (Pi.mulSingle q g) f : P) = s q g f)
    (hop : ∀ q g i, Commute (s q g) (op i)) :
    ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z) :=
  ae_ind _ (fun i z z' h => by simpa using h)
    (fun g g' hg hg' i z z' h => by
      rw [map_mul]
      exact hg i _ _ (hg' i z z' h))
    (fun q g i z z' h => by rw [hρ, hρ, h, ← Module.End.mul_apply, (hop q g i).eq, Module.End.mul_apply])
section Top
variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]
private theorem ae_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩
private theorem ae_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩
end Top
private theorem ae_commU {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]
private theorem ae_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ
private theorem ae_bot {A R P : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] {Y : Submodule A P} (h : Y = ⊥)
    (lam : A → R) : ∃ μ : R →+* Module.End A Y, (∀ b y, μ (lam b) y = b • y) ∧ Subsingleton Y := by
  haveI : Subsingleton Y := h ▸ inferInstance
  exact ⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, this⟩
private theorem ae_mu {O A R P ι : Type} [CommRing O] [CommRing A] [CommRing R] [AddCommGroup P] [Module A P]
    {Y : Submodule A P} {op : ι → Module.End A P} [Fact (CommOn Y op)] [Algebra O R] [Algebra O (heckeAlg Y op)]
    (f : R →ₐ[O] heckeAlg Y op) (lam : A → R) (hl : ∀ b, f (lam b) = algebraMap A _ b) :
    ∃ μ : R →+* Module.End A Y, (∀ t, μ t = (f t : Module.End A Y)) ∧ ∀ b y, μ (lam b) y = b • y := by
  refine ⟨(heckeAlg Y op).val.toRingHom.comp f.toRingHom, fun _ => rfl, fun b y => ?_⟩
  change (f (lam b) : Module.End A Y) y = _
  rw [hl]
  rfl
private theorem ae_nt {A P ι : Type} [CommRing A] [AddCommGroup P] [Module A P] {Y : Submodule A P}
    {op : ι → Module.End A P} [Nontrivial (heckeAlg Y op)] : ¬ Subsingleton Y := fun _ =>
  absurd (inferInstance : Subsingleton (heckeAlg Y op)) (not_subsingleton _)
private theorem ae_zero {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : Subsingleton M) (φ : M →ₗ[A] N) (s : Module.End A M) (t : Module.End A N) (y : M) : φ (s y) = t (φ y) := by
  rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]
end Helpers
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)
private def ae_Ok (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) : Prop :=
  Subsingleton (H.MK θ a K) ∨
    ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
      H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))
private theorem ae_ex (lam : A →ₐ[c.O] R) (K : H.Lev) (J : Ideal R) (hJ : H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ ae_Ok H θ a D₀ ψ₀ K μ := by
  rcases hJ with h | ⟨i1, i2, f, -, hf, -, hl, -⟩
  · exact (ae_bot (A := A) (R := R) (P := H.X.Fn A H.m) (Y := H.MK θ a K) h.1 lam).imp fun μ h => ⟨h.1, .inl h.2⟩
  · exact (ae_mu (A := A) (P := H.X.Fn A H.m) (Y := H.MK θ a K) (op := H.op A) f lam hl).imp
      fun μ h => ⟨h.2, .inr ⟨i1, i2, f, hf, h.1⟩⟩
private theorem ae_cmp (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hH : H.Ax) (hθ : H.IsWt θ)
    (hU : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T),
      D₀.map f.toRingHom = D₀.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (K K' : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (μ' : R →+* Module.End A (H.MK θ a K'))
    (h : ae_Ok H θ a D₀ ψ₀ K μ) (h' : ae_Ok H θ a D₀ ψ₀ K' μ') (φ : H.MK θ a K →ₗ[A] H.MK θ a K') (hφ : Function.Injective φ)
    (hc : ∀ i (y y' : H.MK θ a K), (y' : H.X.Fn A H.m) = H.op A i y → (φ y' : H.X.Fn A H.m) = H.op A i (φ y)) (t : R)
    (y : H.MK θ a K) : φ (μ t y) = μ' t (φ y) := by
  rcases h with h | ⟨i1, i2, f, hf, e⟩
  · exact ae_zero h φ (μ t) (μ' t) y
  rcases h' with h | ⟨i1', i2', f', hf', e'⟩
  · exact h.elim _ _
  rw [e, e']
  exact _root_.UpperTheory.V.Hi.level_change_compat_rank_two_of_dense_weight hN L Ω l n c H hH A θ hθ a K K' R D₀ ψ₀ hU f f' hf hf' φ hφ (fun i y => hc i y _ rfl) t y
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem ae_out (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (h : ae_Ok H θ a D₀ ψ₀ K μ)
    [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] :
    ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K)) := by
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h (ae_nt (op := H.op A))
  · exact h
private theorem ae_op (hH : H.Ax) (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with x | x
  · exact ae_dc _ _ _ (hH.sectionsCommuteAtSplit q _ x.1.2 g) _ _ _
  · exact ae_commU _ _ _ _
end
theorem UpperTheory.V.Hi.levelUR2ActEx_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) → (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) → ∀ (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → (∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) → ∃ α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ ∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _ ρ hρ hfix hex R _ _ D₀ ψ₀ lam hU hJ
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  choose μ hμ1 hμ2 using fun K => ae_ex H θ a D₀ ψ₀ lam K _ (hJ K).choose_spec
  obtain ⟨α, h1, h2⟩ := ae_abs (H.MK θ a) _ (H.op A) ρ (fun K : H.Lev => Subgroup.pi Set.univ K.1) hfix hex ae_inf ae_conj
    (ae_gen _ (H.op A) ρ (fun q g => H.X.ra (H.τA A) (H.sec (H.wq q) g)) hρ (ae_op H hH)) μ
    (fun K K' => ae_cmp H θ a D₀ ψ₀ hN hH hθ hU K K' _ _ (hμ2 K) (hμ2 K'))
  refine ⟨α, fun b z => ?_, h1, fun K i1 i2 => ?_⟩
  · obtain ⟨K, hK⟩ := hex z
    exact Subtype.ext ((h2 K _ ⟨z, hK⟩ z rfl).trans (congrArg Subtype.val (hμ1 K b ⟨z, hK⟩)))
  · obtain ⟨f, hf, e⟩ := ae_out H θ a D₀ ψ₀ K _ (hμ2 K)
    refine ⟨f, hf, fun t y z hz => ?_⟩
    rw [← e]
    exact h2 K t y z hz
end
end

section




section
open Formalism.GaloisCohomology
namespace UpperTheory.V.ZK
theorem lemmaK_of_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hB : BOdd) : ∃ CK, LemmaK CK :=
  lemmaK hB (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK
end UpperTheory.V.ZK
end
end

section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.unramified_of_split_distinct_characters :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : Submodule ℂ (UA L n → ℂ)) (w : Plc L) (ψ : Fin n → (Kw w)ˣ →* ℂˣ), IsSplitAt w → CompSub π w ψ →
        (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) → (∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow (Kw w) 1) → IsUnramU π w := by
  intro H L _ _ _ n π w ψ hw hc hu hne
  obtain ⟨hsm, τ, ⟨-, f, hf0, hfπ, hf⟩, hsq⟩ := hc
  obtain ⟨hs1, hs2, -, -⟩ := secSpec L n w hw
  have hker : ∀ x, f x = 0 → x = 0 := by
    let S : Subrepresentation τ.ρ := ⟨LinearMap.ker f, by
      intro g x hx
      have h := hf ⟨secW n w g, hs1 g⟩ x
      have h' : f (τ.ρ g x) = RU L n (secW n w g) (f x) := by
        rw [← h]
        show f (τ.ρ g x) = f (τ.ρ (cLoc w (secW n w g)) x)
        rw [hs2 g]
      rw [LinearMap.mem_ker] at hx ⊢
      rw [h', hx, map_zero]⟩
    have hS : S = ⊥ := by
      rcases (τ.irred.eq_bot_or_eq_top S) with h | h
      · exact h
      · refine absurd (LinearMap.ext fun x => ?_) hf0
        have : x ∈ S.toSubmodule := by rw [h]; trivial
        exact this
    intro x hx
    have : x ∈ S.toSubmodule := hx
    rw [hS] at this
    exact this
  obtain ⟨ω, rfl, hω⟩ : ∃ ω : Fin n → (Kw w)ˣ →* ℂˣ,
      ψ = (fun i => ω i * absPow (Kw w) (((n : ℂ) - 1) / 2)) ∧ ∀ i, IsSmoothChar (ω i) := by
    refine ⟨fun i => ψ i * absPow (Kw w) (-(((n : ℂ) - 1) / 2)), funext fun i => ?_,
      fun i => (hsm i).mul (isSmoothChar_of_isUnram (isUnram_absPow _ _))⟩
    have h0 : absPow (Kw w) 0 = 1 := by
      ext x
      simp [absPow]
    rw [mul_assoc, ← absPow_add, neg_add_cancel, h0, mul_one]
  have hneω : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (Kw w) 1 := fun i j hij =>
    ⟨fun h => (hne i j hij).1 (by simp only [h]), fun h => (hne i j hij).2 (by
      simp only []
      rw [h, mul_right_comm])⟩
  have hE : Nonempty (τ.ρ.Equiv (UpperTheory.V.Hi.PS ω)) :=
    (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H (Kw w) n ω hω hneω).2 _ τ.ρ τ.irred hsq
  obtain ⟨E⟩ := hE
  obtain ⟨v₀, hv₀, hfix⟩ := locSph (Kw w) n _ hu
  obtain ⟨v, rfl⟩ := E.surjective v₀
  have hv : v ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero E)
  have hτ : ∀ u ∈ KO (Kw w) (Fin n), τ.ρ u v = v := fun u hu' => by
    apply E.injective
    have h1 := LinearMap.congr_fun (E.isIntertwining' u) v
    exact h1.trans (hfix u hu')
  refine ⟨f v, hfπ v, fun h => hv (hker v h), fun x hx hK => ?_⟩
  have h := hf ⟨x, hx⟩ v
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL] at hK
  rw [← h]
  show f (τ.ρ (cLoc w x) v) = f v
  rw [hτ _ hK]
end
end

section




section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.regular_algebraic_and_polarized_of_quadratic_base_change : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K], Module.finrank F K = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (χ : HChar F) (P : CuspSub K a), π.IsRegAlg → π.Polarized χ → IsBC π P → (CG.mk P).IsRegAlg ∧ ∃ χ' : HChar (maximalRealSubfield K), GlobalTheory.ContraPair.PolarizedPair P χ' := by
  first | exact @_root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt | exact _root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt | (intros; apply _root_.GlobalTheory.BcPolar.bc_regAlg_polarizedPair_alt <;> assumption)
end
end

section




section
namespace UpperTheory.V.Af
open UpperTheory.V.Published
structure Hypotheses' : Prop where
  litN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis
  cohC : ClozelCohC
  conjC : ClozelConjC
  borelC : BorelInjC
  galR : _root_.UpperTheory.Gal.SV.GaloisRepExistsTotallyRealGL2
  smoR : StrongMultOneReal
  gkR : GelfandKazhdanReal
  admR : AdmissibleReal
  bc : Br.QuadBC0
  newform : NewformRep
end UpperTheory.V.Af
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix
namespace UpperTheory.V.Sd
def Seed2Alt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (N w : ℕ) (χ' η θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ (κ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ) (ka : _root_.Formalism.ConjugateSelfDual.G L Ω →* (Qbar l)ˣ), IsTwist ι c κ →
    (∀ (s : _root_.Formalism.ConjugateSelfDual.G L Ω) (s' : _root_.Formalism.ConjugateSelfDual.G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ σ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous σ ∧
      Matrix.GeneralLinearGroup.det.comp σ = η * θ ∧ ResSum σ ![cycBar ℚ Ω l ^ j * χ' * η, (cycBar ℚ Ω l ^ j * χ')⁻¹] ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), -(m : ℤ)] ka (σ.comp (galEmb ℚ L Ω))
end UpperTheory.V.Sd
end
end
end
