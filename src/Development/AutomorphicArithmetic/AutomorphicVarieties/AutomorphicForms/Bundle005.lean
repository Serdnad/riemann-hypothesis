module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af.Wd

def IsTri {k W ι : Type} [Field k] [AddCommGroup W] [Module k W] {n : ℕ} (T : ι → End k W) (d : ι → Fin n → k) : Prop :=
  ∃ b : Basis (Fin n) k W, ∀ a, (∀ i j, j < i → LinearMap.toMatrix b b (T a) i j = 0) ∧
    ∀ i, LinearMap.toMatrix b b (T a) i i = d a i

def ops {Γ R : Type} (N : R) (ρ : Γ → R) : Option Γ → R := fun a => a.elim N ρ

@[simp] theorem ops_none {Γ R : Type} (N : R) (ρ : Γ → R) : ops N ρ none = N := rfl

def cycL {l : ℕ} [Fact l.Prime] (L : FinExt l) : GQ l →* (↥L.1)ˣ :=
  (Units.map (algebraMap ℚ_[l] ↥L.1 : ℚ_[l] →* ↥L.1)).comp (Loc.PP l).χQ

def FrobPow {l : ℕ} [Fact l.Prime] (g : GQ l) (k : ℕ) : Prop :=
  ∀ c : ↥(MaximalUnramifiedExtension l), g (c : Om l) = (((frobUr l ^ k) c : ↥(MaximalUnramifiedExtension l)) : Om l)

def TriSnoc : Prop :=
  ∀ (k W' W W'' ι : Type) [Field k] [AddCommGroup W'] [Module k W'] [AddCommGroup W] [Module k W] [AddCommGroup W'']
    [Module k W''] (n : ℕ) (T' : ι → End k W') (T : ι → End k W) (T'' : ι → End k W'') (f : W' →ₗ[k] W) (p : W →ₗ[k] W''),
    Function.Injective f → Function.Surjective p → Function.Exact f p → finrank k W'' = 1 →
    (∀ a x, f (T' a x) = T a (f x)) → (∀ a x, p (T a x) = T'' a (p x)) → ∀ d : ι → Fin (n + 1) → k,
    IsTri T' (fun a i => d a (Fin.castSucc i)) → (∀ a y, T'' a y = d a (Fin.last n) • y) → IsTri T d

def TriInit : Prop :=
  ∀ (k W ι : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (T : ι → End k W) (d : ι → Fin (n + 1) → k), IsTri T d →
    ∃ (S : Submodule k W) (hS : ∀ a, ∀ x ∈ S, T a x ∈ S) (p : W →ₗ[k] k), Function.Surjective p ∧ LinearMap.ker p = S ∧
      (∀ a x, p (T a x) = d a (Fin.last n) * p x) ∧ IsTri (fun a => (T a).restrict (hS a)) (fun a i => d a (Fin.castSucc i))

def TriMono : Prop :=
  ∀ (k W Γ : Type) [Field k] [AddCommGroup W] [Module k W] (n : ℕ) (N : End k W) (ρ : Γ → End k W) (c : Γ → k)
    (μ : Γ → Fin n → k), (∀ σ, ρ σ * N = c σ • (N * ρ σ)) → IsTri (ops N ρ) (ops 0 μ) → N ≠ 0 →
    ∃ i j, ∀ σ, μ σ i = c σ * μ σ j

def TriDiag : Prop :=
  ∀ (W I : Type) [AddCommGroup W] [Module ℂ W] [Group I] (n : ℕ) (ρ : I →* End ℂ W) (d : I → Fin n → ℂ),
    (Set.range ρ).Finite → IsTri (fun s => ρ s) d →
    ∃ b : Basis (Fin n) ℂ W, ∀ s, LinearMap.toMatrix b b (ρ s) = Matrix.diagonal (d s)

def LetterExact : Prop :=
  ∀ (LL U D' D D'' F : Type) [Field LL] [Field U] [AddCommGroup D'] [Module LL D'] [AddCommGroup D] [Module LL D]
    [AddCommGroup D''] [Module LL D''] [Field F] [Algebra LL F] (m' : U →+* End LL D') (m : U →+* End LL D)
    (m'' : U →+* End LL D'') (τ : U →+* F) (T : D' →ₗ[LL] D) (S : D →ₗ[LL] D'') (hT : ∀ c, T ∘ₗ m' c = m c ∘ₗ T)
    (hS : ∀ c, S ∘ₗ m c = m'' c ∘ₗ S), Function.Exact T S → Function.Surjective S →
    Function.Exact (letterLin m' m F τ T hT) (letterLin m m'' F τ S hS) ∧ Function.Surjective (letterLin m m'' F τ S hS)

def DLeft : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Exact f p →
    Function.Injective (dmap P hf) ∧ Function.Exact (dmap P hf) (dmap P hp)

def DRight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (_ : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Surjective (dmap (Loc.PP l) hp)

def WdExact : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Om l ≃+* ℂ) (K L : FinExt l) (V' V V'' : Type)
    [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    [AddCommGroup V''] [Module ↥L.1 V''] [Module ℚ_[l] V''] [IsScalarTower ℚ_[l] ↥L.1 V'']
    (ρ' : Representation ↥L.1 ↥(GK K) V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ'' : Representation ↥L.1 ↥(GK K) V'')
    (f : V' →ₗ[↥L.1] V) (p : V →ₗ[↥L.1] V'') (hf : ∀ g v, f (ρ' g v) = ρ g (f v)) (hp : ∀ g v, p (ρ g v) = ρ'' g (p v)),
    Function.Injective f → Function.Surjective p → Function.Exact f p → IsPst (Loc.PP l) ρ →
    IsPst (Loc.PP l) ρ' ∧ IsPst (Loc.PP l) ρ'' ∧ Function.Injective (wdLin (Loc.PP l) ι hf) ∧
      Function.Surjective (wdLin (Loc.PP l) ι hp) ∧ Function.Exact (wdLin (Loc.PP l) ι hf) (wdLin (Loc.PP l) ι hp)

def WdTri : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (n : ℕ) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (κ : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ)
    (μ : ↥(Weil h) → Fin n → ℂ), IsTri (fun g => ρ g) (fun g i => (κ i g : ↥L.1)) →
    (∀ i (hi : IsPst (Loc.PP l) (Loc.chRep (κ i))) σ y,
      haveI := hi.finite; wdRho (Loc.PP l) ι Bw h hj (Loc.chRep (κ i)) σ y = μ σ i • y) →
    ∀ hV : IsPst (Loc.PP l) ρ,
      haveI := hV.finite; IsTri (ops (wdN (Loc.PP l) ι ρ) fun σ => wdRho (Loc.PP l) ι Bw h hj ρ σ) (ops 0 μ)

def Line : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
    [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V), finrank ↥L.1 V = 1 → ∀ (hV : IsPst P ρ)
    (x : ↥(Dpst P ρ)), x ≠ 0 → ∀ c : ↥L.1, c ≠ 0 →
    (phiD P ρ ^ resDeg l w) x = (Dpst P ρ).module.toSMul.smul c x →
    ∀ (σ : ↥(Weil h)) (s : ↥L.1),
      actD P ρ (weilToGK Bw h σ) x = (Dpst P ρ).module.toSMul.smul s x → ∀ y,
      haveI := hV.finite; wdRho P ι Bw h hj ρ σ y = ι ((c ^ (-deg σ) * s : ↥L.1) : Om l) • y

def TiltFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → ∀ (g : GQ l) (k : ℕ), FrobPow g k →
    (Loc.AIP l).actT g y = y ^ l ^ k

def WittPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Loc.Bcr l), IsUnit W.det ∧
      (∀ g, (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).actQ (g : GQ l)) = W) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        (M g).map (fun z => algebraMap ℚ_[l] (Loc.Bcr l) (z : ℚ_[l])) * W.map ((Loc.PP l).φB ^ k) = W

def IntBasis : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (V : Type) [AddCommGroup V]
    [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] Γ V), (∀ x, Continuous fun g => ρ g x) →
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V) (M : Γ →* Matrix (Fin n) (Fin n) ℤ_[l]), Continuous M ∧
      ∀ g i j, ((M g i j : ℤ_[l]) : ℚ_[l]) = e.repr (ρ g (e j)) i

def UnrPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (η : ↥(GK K) →* (↥L.1)ˣ), Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ u : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), u ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep η) g u = u) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k → (η g : ↥L.1) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) u = u

def TwistPer : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (κ χ η : ↥(GK K) →* (↥L.1)ˣ) (m : ℤ),
    (∀ g, κ g = cycL L (g : GQ l) ^ m * χ g * η g) → Continuous (fun g => ((η g : ↥L.1) : Om l)) →
    (∀ g : ↥(GK K), (g : GQ l) ∈ Loc.Iq l → η g = 1) → ∃ y : ↥L.1 ⊗[ℚ_[l]] Bst (Loc.PP l), y ≠ 0 ∧
      (∀ g, stRep (Loc.PP l) (Loc.chRep κ) g y = (χ g : ↥L.1) • y) ∧
      ∀ (g : ↥(GK K)) (k : ℕ), FrobPow (g : GQ l) k →
        ((η g : ↥L.1) * (l : ↥L.1) ^ (m * k)) • (phiV (Loc.PP l) ↥L.1 ↥L.1 ^ k) y = y

def BrFacts : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw →
    FrobPow (weilToGK Bw h (frob h) : GQ l) (resDeg l w) ∧
    (∀ (L : FinExt l) (s : ↥(Dec (F := F) A)), ((cycL L (Bw.e s : GQ l) : ↥L.1) : Om l) = (cycBar F Ω l s : Qbar l)) ∧
    ∀ M : ℕ, 1 ≤ M → ∃ K' : FinExt l, ∀ s : ↥(Dec (F := F) A), (Bw.e s : GQ l) ∈ GK K' →
      ∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ

def CharWD : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Om l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (L : FinExt l) (κ χ : ↥(GK Bw.Kw) →* (↥L.1)ˣ) (m : ℤ), Continuous (fun g => ((κ g : ↥L.1) : Om l)) →
    (∃ K' : FinExt l, ∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ GK K' → χ g = 1) →
    (∀ g : ↥(GK Bw.Kw), (g : GQ l) ∈ Loc.Iq l → κ g = cycL L (g : GQ l) ^ m * χ g) →
    ∀ (hκ : IsPst (Loc.PP l) (Loc.chRep κ)) (σ : ↥(Weil h)) y,
      haveI := hκ.finite
      wdRho (Loc.PP l) ι Bw h hj (Loc.chRep κ) σ y = (((normV w : ℕ) : ℂ) ^ (m * deg σ) *
        ι (((κ (weilToGK Bw h σ) * cycL L (weilToGK Bw h σ : GQ l) ^ (-m) : (↥L.1)ˣ) : ↥L.1) : Om l)) • y

def WeilDense : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    DenseRange (Subgroup.inclusion (Weil_le_Dec h))

def CharEnd : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), w ∈ placesOver F l →
    ∀ (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℤ), Continuous (fun s => (ψ s : Qbar l)) →
    (∀ σ : ↥(Weil h), ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) = ((normV w : ℕ) : ℂ) ^ (a * deg σ)) →
    a = 0 ∧ ψ = 1

def FinVal : Prop :=
  ∀ (F Ω C : Type) [Field F] [Field Ω] [Algebra F Ω] [Group C] (M : ℕ), 1 ≤ M → ∀ χ : G F Ω →* C, KillsMu M χ →
    (Set.range χ).Finite

def Model : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, (Set.range (χ i)).Finite) →
    IsFlagOn r (Dec (F := F) A) κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
    ∃ (L : FinExt l) (ρ : Representation ↥L.1 ↥(GK Bw.Kw) (Fin n → ↥L.1)) (κL χL : Fin n → ↥(GK Bw.Kw) →* (↥L.1)ˣ),
      IsPst (Loc.PP l) ρ ∧ wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = wdPst (Loc.PP l) ι Bw h hj ρ ∧
      IsTri (fun g => ρ g) (fun g i => (κL i g : ↥L.1)) ∧
      (∀ i s, ((κL i (Bw.e s) : ↥L.1) : Om l) = (κ i s : Qbar l)) ∧
      ∀ i (s : ↥(Dec (F := F) A)), ((χL i (Bw.e s) : ↥L.1) : Om l) = (χ i s : Qbar l)

end UpperTheory.V.Af.Wd
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Sys

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}


variable (n) in
def IsCusp (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  (∃ (_ : IsTotallyComplex F) (π : CuspSub F n), sat = (CG.mk π).HasSat ∧ inf = π.HasInfChar) ∨
    ∃ (_ : IsTotallyReal F) (π : TR.CuspSub F n), sat = π.HasSat ∧ inf = fun τ => π.HasInfChar (InfinitePlace.mk τ)


omit [NumberField F] in
variable (n) in
def RegInf (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  ∀ τ, ∃ m, inf τ m ∧ m.Nodup ∧ ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2

def IsAut (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ sat inf, IsCusp n sat inf ∧ RegInf n inf ∧ AttachedSys ι r sat

def IsCharOf [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (μ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles F →* Gab F Ω) (a : (F →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ a ∧ IsLAdicOf art ι χ a μ

def IsAlgChar [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (μ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ) : Prop := ∃ χ : HChar F, IsCharOf ι χ μ


omit [NumberField F] in
def IsConjEl (c : _root_.Formalism.ConjugateSelfDual.G F Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

end Sys

section Pol

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsPairing (c : _root_.Formalism.ConjugateSelfDual.G F₀ Ω) (r : _root_.Formalism.ConjugateSelfDual.G F Ω →* GL (Fin n) k) (μ : _root_.Formalism.ConjugateSelfDual.G F Ω →* kˣ) (P : GL (Fin n) k) : Prop :=
  ∀ s s' : _root_.Formalism.ConjugateSelfDual.G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
    (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
      (μ s : k) • (P : Matrix (Fin n) (Fin n) k)


variable (F₀ F) in
abbrev resG (Ω : Type) [Field Ω] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω] : _root_.Formalism.ConjugateSelfDual.G F Ω →* _root_.Formalism.ConjugateSelfDual.G F₀ Ω :=
  AlgEquiv.restrictScalarsHom F₀

end Pol

def IsPlusOf (F₀ F : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F] : Prop :=
  IsTotallyReal F₀ ∧ (Module.finrank F₀ F = 1 ∨ (Module.finrank F₀ F = 2 ∧ IsTotallyComplex F))

section Quat

variable (F : Type) [Field F] [NumberField F]

structure DefQuat : Type 1 where

  D : Type
  [ring : DivisionRing D]
  [alg : Algebra F D]
  central : Algebra.IsCentral F D
  rank : Module.finrank F D = 4

  definite : ∀ τ : F →+* ℝ, letI := τ.toAlgebra; NoZeroDivisors (ℝ ⊗[F] D)

  jf : D →ₐ[F] Matrix (Fin 2) (Fin 2) (Af F)
  jf_bij : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId (Af F) (Matrix (Fin 2) (Fin 2) (Af F))) jf
    fun _ _ => Algebra.commutes _ _)

  jc : InfinitePlace F → D →+* Matrix (Fin 2) (Fin 2) ℂ
  jc_alg : ∀ v x, jc v (algebraMap F D x) = algebraMap ℂ _ (v.embedding x)

attribute [instance] DefQuat.ring DefQuat.alg

variable {F}

namespace DefQuat

variable (Q : DefQuat F)

def toFin : Q.Dˣ →* GL (Fin 2) (Af F) := Units.map Q.jf.toRingHom.toMonoidHom

end DefQuat

end Quat

end UpperTheory.V.Af
end
end

section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AutOn (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) (j : ℤ)
    (a : G ℚ Ω → Matrix (Fin n) (Fin n) (Qbar l)) : Prop :=
  ∃ (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (ρ : G K Ω →* GL (Fin n) (Qbar l)),
    (∀ s : G K Ω, (ρ s : Matrix (Fin n) (Fin n) (Qbar l)) = a (s.restrictScalars ℚ)) ∧ IsAutCsd ι (tw ρ (cycBar K Ω l ^ j))

end UpperTheory.V.Af
end
end

section

noncomputable section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N

namespace UpperTheory.V.Af

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ 3
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

end TrData

end UpperTheory.V.Af
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

def infOf {n : ℕ} (m : Fin n → ℤ) : Multiset ℂ := Finset.univ.val.map fun i => ((n : ℂ) - 1) / 2 + (m i : ℂ)

def SigK (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ GlobalTheory.ContraPair.DualIsConj π ∧ HasFixed π.finPart (KLev K n M)}

def SigQ {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (TR.CuspSub ℚ n) :=
  {π | (∀ v, π.HasInfChar v (infOf m)) ∧ (∃ χ : HChar ℚ, π.IsSelfDualBy χ) ∧ HasFixed π.finPart (KLev ℚ n M)}

def CardK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigK K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def ConjK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigK K m M, ∃ π' ∈ SigK K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def SatK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n M : ℕ) (π : CuspSub K n), HasFixed π.finPart (KLev K n M) →
    ∀ w : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B

def SlopesIn {n : ℕ} (q : ℕ) (m : Fin n → ℤ) (B : Multiset ℂ) : Prop :=
  ∀ b ∈ B, (∀ a : ℤ, (∀ i, -a ≤ m i) → IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)) ∧
    ∀ a : ℤ, (∀ i, m i ≤ a) → IsIntegral ℤ ((q : ℂ) ^ a * b)

def IntK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigK K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def IntQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigQ m M, ∀ w : HeightOneSpectrum (𝓞 ℚ), (M : 𝓞 ℚ) ∉ w.asIdeal →
      ∀ B, π.HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def IsoOfFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' →
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) → RepIso r r'

end UpperTheory.V.Af
end
end
