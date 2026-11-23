module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Bilinear

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

end Bilinear

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

end Generic

def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie

def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)

end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def CmpIso (W : LocWach PD LL O v n) (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 ↔ ∃ y : ↥(W.N T), x = (letπ : LetA O n) • y) ∧
  Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) = Dcris PD T.ρ ∧
  (∀ i : ZMod n, Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x))
      = DcrisL PD T.ρ (W.emb i)) ∧
  (∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
    W.cmp T ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ =
      (l : LL) ^ m • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
end
end

section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} (R : Fr l O)

def diag (n : ℕ) (a : O⟦X⟧) : LetA O n := fun _ => a

def KillsN {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (i : ZMod n) (a : O⟦X⟧) : Prop :=
  ∀ y ∈ W.Nl T' i, ∃ x ∈ W.Nl T i, W.map f x = diag n a • y

variable [NeZero n] {R} (jE : R.EE →ₐ[O] W.EE)

def vec {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) (x : DD R n r) : W.DD T :=
  ∑ i, ∑ k, jE (x i k) • b i k



end Generic

variable {l : ℕ} [Fact l.Prime]

instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Emb (K LL : FinExt l) : Type := ↥K.1 →ₐ[ℚ_[l]] ↥LL.1

def embeddingRestrictMaxUnramified {K LL : FinExt l} (τ : Emb K LL) : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

section Objects

variable (P : LocPrime l) {K LL : FinExt l}

abbrev iota (T : Lat K LL) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  ιV (P.PD K) (LL := ↥LL.1) (V := T.V)

abbrev filV (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a

abbrev mulK (T : Lat K LL) (c : ↥K.1) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  mulVdR (Qp := ℚ_[l]) (K := ↥K.1) (BdR := P.R.BdR) (LL := ↥LL.1) (V := T.V) c

def filD (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  DdR (P.PD K) T.ρ ⊓ filV P T a

def tdR (K : FinExt l) : P.R.BdRˣ := ((P.PD K).t_unit.map (P.PD K).ι).unit

def offComp (T : Lat K LL) (τ : Emb K LL) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  Submodule.span ↥LL.1 {z | ∃ (c : ↥K.1), ∃ y ∈ DdR (P.PD K) T.ρ, z = mulK P T c y - τ c • y}

def mapdR {T T' : Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T'.V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)

end Objects

section Shapes

variable {K LL : FinExt l}

def IsSES {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V) : Prop :=
  (∀ σ x, f (T₀.ρ σ x) = T₁.ρ σ (f x)) ∧ (∀ σ x, g (T₁.ρ σ x) = T₂.ρ σ (g x)) ∧
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def IsDualRep {T T' : Lat K LL} (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1) : Prop :=
  (∀ σ x y, β (T.ρ σ x) (T'.ρ σ y) = β x y) ∧ Function.Bijective β.flip

def IsTensorRep {T₁ T₂ T₃ : Lat K LL} (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V) : Prop :=
  ∀ σ x y, T₃.ρ σ (e (x ⊗ₜ[↥LL.1] y)) = e (T₁.ρ σ x ⊗ₜ[↥LL.1] T₂.ρ σ y)

def SubSES (P : LocPrime l) {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (g : T₁.V →ₗ[↥LL.1] T₂.V) (A₀ : Submodule ↥LL.1 (T₀.V ⊗[ℚ_[l]] P.R.BdR))
    (A₁ : Submodule ↥LL.1 (T₁.V ⊗[ℚ_[l]] P.R.BdR))
    (A₂ : Submodule ↥LL.1 (T₂.V ⊗[ℚ_[l]] P.R.BdR)) : Prop :=
  (∀ x ∈ A₀, mapdR P f x = 0 → x = 0) ∧
    (∀ y, (∃ x ∈ A₀, mapdR P f x = y) ↔ (y ∈ A₁ ∧ mapdR P g y = 0)) ∧
    (∀ z, (∃ y ∈ A₁, mapdR P g y = z) ↔ z ∈ A₂)

end Shapes

section At

variable (P : LocPrime l) (K LL : FinExt l)

def CrysDeRhamAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → IsDR (P.PD K) T.ρ

def DdRSpanAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    DdR (P.PD K) T.ρ = Submodule.span ↥LL.1
      {z | ∃ (c : ↥K.1), ∃ x ∈ Dcris (P.PD K) T.ρ, z = mulK P T c (iota P T x)}

def ComponentIsoAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → ∀ τ : Emb K LL,
    ∃ e : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)) ≃ₗ[↥LL.1] ↥(DdRE (P.PD K) T.ρ τ),
      ∀ x : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)), iota P T (x : T.V ⊗[ℚ_[l]] P.R.B) - (e x : T.V ⊗[ℚ_[l]] P.R.BdR) ∈ offComp P T τ

def UnramOntoAt : Prop :=
  K.1 ≤ MaximalUnramifiedExtension l → ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    (Dcris (P.PD K) T.ρ).map (iota P T) = DdR (P.PD K) T.ρ

def FilZeroAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    filV P T 0 = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil 0, ∃ d ∈ filD P T a,
        z = mulVR T (((tdR P K ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b) d}

def StrictAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ (τ : Emb K LL) (a : ℤ), SubSES P f g
      (FildR (P.PD K) T₀.ρ τ a) (FildR (P.PD K) T₁.ρ τ a) (FildR (P.PD K) T₂.ρ τ a)

def DualJumpsAt : Prop :=
  ∀ (T T' : Lat K LL) (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1), IsDualRep β →
    IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ a ↔ IsJumpV (P.PD K) T.ρ τ (-a)) ∧
        multV (P.PD K) T'.ρ τ a = multV (P.PD K) T.ρ τ (-a)

def TensorJumpsAt : Prop :=
  ∀ (T₁ T₂ T₃ : Lat K LL) (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V), IsTensorRep e →
    IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    IsDR (P.PD K) T₃.ρ ∧ ∀ (τ : Emb K LL) (c : ℤ),
      (IsJumpV (P.PD K) T₃.ρ τ c ↔
        ∃ a b : ℤ, IsJumpV (P.PD K) T₁.ρ τ a ∧ IsJumpV (P.PD K) T₂.ρ τ b ∧ a + b = c) ∧
      ∀ S : Finset ℤ, JumpsInV (P.PD K) T₁.ρ τ (S : Set ℤ) →
        multV (P.PD K) T₃.ρ τ c =
          ∑ a ∈ S, multV (P.PD K) T₁.ρ τ a * multV (P.PD K) T₂.ρ τ (c - a)

def TwistJumpsAt : Prop :=
  ∀ T T' : Lat K LL, IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ → IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ (a - 1) ↔ IsJumpV (P.PD K) T.ρ τ a) ∧
        multV (P.PD K) T'.ρ τ (a - 1) = multV (P.PD K) T.ρ τ a

def PotCrysDeRhamAt : Prop :=
  ∀ (T : Lat K LL) (K' : FinExt l) (hK : K.1 ≤ K'.1),
    IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hK))) → IsDR (P.PD K) T.ρ

end At

def OverGood (C : FinExt l → FinExt l → Prop) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → C K LL

section Good

variable (l) (P : LocPrime l)

def CrysDeRham : Prop := OverGood (CrysDeRhamAt P)
def DdRSpan : Prop := OverGood (DdRSpanAt P)
def ComponentIso : Prop := OverGood (ComponentIsoAt P)
def UnramOnto : Prop := OverGood (UnramOntoAt P)
def FilZero : Prop := OverGood (FilZeroAt P)
def Strict : Prop := OverGood (StrictAt P)
def DualJumps : Prop := OverGood (DualJumpsAt P)
def TensorJumps : Prop := OverGood (TensorJumpsAt P)
def TwistJumps : Prop := OverGood (TwistJumpsAt P)
def PotCrysDeRham : Prop := OverGood (PotCrysDeRhamAt P)

def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DdRSpan l P ∧ ComponentIso l P ∧ UnramOnto l P ∧ FilZero l P ∧ Strict l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P

end Good

end GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Core

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Ops

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)

def tdR : BdRˣ := (PD.t_unit.map PD.ι).unit

variable (ρ : Representation LL G V)

def filDdR (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) := DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a

def jumpMult (τ : K →ₐ[Qp] LL) (a : ℤ) : ℕ :=
  Module.finrank LL (↥(FildR PD ρ τ a) ⧸ (FildR PD ρ τ (a + 1)).comap (FildR PD ρ τ a).subtype)

end Ops

variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]

def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ

def SpanCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    DdR PD T.ρ = ⨆ c : K, ((Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V))).map
      (mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) c)

def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a

end Core

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)

def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
end
end
