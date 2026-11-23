module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleCover.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (F : SubSystem S x Ω),
    (∀ (j : Fin (A.r + 1)) (I : Chart x) (y : Ω), y ∈ F.sub I → ∃ e : ℕ,
      y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) (F.secs : Set Ω) * (H.pow (A.m * e)).sub I) →
    F.Generated

def AmpleTwistLocal.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)),
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (I : Chart x) (y : Ω), y ∈ (Q.twist (H.pow (b + A.m * n))).sub I →
      ∃ e : ℕ, y * A.h j ^ e ∈
        Submodule.span (chartRing S x I) ((Q.twist (H.pow (b + A.m * n))).secs : Set Ω) *
          (H.pow (A.m * e)).sub I

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (x : Fin (N + 1) → Ω)

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def AmpleAffineGen.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (A : AmpleData S x H) (Q : LineBundle S x) (b : ℕ)
    (j : Fin (A.r + 1)), A.h j ≠ 0 →
    ∃ (p : ℕ) (s : Fin p → Ω),
      (∀ (t : Fin p) (I : Chart x), ∃ k : ℕ,
        s t * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I) ∧
      ∀ (I : Chart x) (z : Ω) (k : ℕ), z * A.h j ^ k ∈ (Q.twist (H.pow (b + A.m * k))).sub I →
        ∃ (e : ℕ) (g : Fin p → Ω), (∀ t, g t * A.h j ^ e ∈ (H.pow (A.m * e)).sub I) ∧
          z = ∑ t, g t * s t

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def CechDSq.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R] (G : Cell U → Type v)
    [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J),
    (∀ (I J K : Cell U) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1),
      (ρ J K hJK).comp (ρ I J hIJ) = ρ I K (hIJ.trans hJK)) →
    ∀ (i : ℕ) (s : Cech.Cochain G i), Cech.d G ρ (i + 1) (Cech.d G ρ i s) = 0

section Hypotheses

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

theorem locResS_comp (I J K : StdCell N) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (locResS (S := S) (M := M) J K hJK).comp (locResS I J hIJ) = locResS I K (hIJ.trans hJK) := by
  refine LinearMap.ext fun x => ?_
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locRes hJK (locRes hIJ _) = locRes (hIJ.trans hJK) _
    rw [locRes_mk, locRes_mk, locRes_mk]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

def DegLocExact.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M' M M'' : Type v)
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M''] [Module (Poly S N) M''] [Module S M''] [IsScalarTower S (Poly S N) M'']
    (𝓜' : GradedPMod S N M') (𝓜 : GradedPMod S N M) (𝓜'' : GradedPMod S N M'')
    (f : GradedHom 𝓜' 𝓜) (g : GradedHom 𝓜 𝓜''),
    Function.Injective f.toLin → Function.Surjective g.toLin → Function.Exact f.toLin g.toLin →
    ∀ (c : ℤ) (I : StdCell N),
      (∀ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = 0 →
        ∃ z' ∈ degLoc 𝓜' c I, locMap f.toLin I.1 z' = z) ∧
      (∀ z'' ∈ degLoc 𝓜'' c I, ∃ z ∈ degLoc 𝓜 c I, locMap g.toLin I.1 z = z'')

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def GradedPres.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (M : Type (max u v))
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module (Poly S N) F) (_ : Module S F)
      (_ : IsScalarTower S (Poly S N) F) (K : Type (max u v)) (_ : AddCommGroup K)
      (_ : Module (Poly S N) K) (_ : Module S K) (_ : IsScalarTower S (Poly S N) K)
      (𝓕 : GradedPMod S N F) (𝓚 : GradedPMod S N K) (r : ℕ) (b : Module.Basis (Fin r) (Poly S N) F)
      (d : Fin r → ℤ) (f : GradedHom 𝓚 𝓕) (g : GradedHom 𝓕 𝓜),
      (∀ j, b j ∈ 𝓕.piece (d j)) ∧ Module.Finite (Poly S N) K ∧ Function.Injective f.toLin ∧
        Function.Surjective g.toLin ∧ Function.Exact f.toLin g.toLin

def GradedULift.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (𝓜 : GradedPMod S N M),
    ∃ (M' : Type (max u v)) (_ : AddCommGroup M') (_ : Module (Poly S N) M') (_ : Module S M')
      (_ : IsScalarTower S (Poly S N) M') (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜')
      (g : GradedHom 𝓜' 𝓜), Function.LeftInverse g.toLin f.toLin ∧ Function.RightInverse g.toLin f.toLin

def CohomRetract.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ) (M : Type v) (M' : Type w)
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
    (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S N M') (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜),
    Function.LeftInverse g.toLin f.toLin → ∀ (i : ℕ) (c : ℤ), Function.Injective (cohomMap f i c)

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def Cech.idRes (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] {n : ℕ}
    (U : Finset (Fin n)) : ∀ I J : Cell U, I.1 ⊆ J.1 → V →ₗ[R] V :=
  fun _ _ _ => LinearMap.id

section Laurent

variable (S : Type u) [CommRing S] (N : ℕ)

abbrev Laurent : Type u := (Fin (N + 1) → ℤ) →₀ S

def laurentExps (c : ℤ) (I : Finset (Fin (N + 1))) : Set (Fin (N + 1) → ℤ) :=
  {a | ∑ j, a j = c ∧ ∀ j ∉ I, 0 ≤ a j}

def laurentDeg (c : ℤ) (I : StdCell N) : Submodule S (Laurent S N) :=
  Finsupp.supported S S (laurentExps N c I.1)

def laurentCohom (i : ℕ) (c : ℤ) : Type u :=
  Cech.Hdeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
    (Cech.idRes S (Laurent S N) Finset.univ) i

instance (i : ℕ) (c : ℤ) : AddCommGroup (laurentCohom S N i c) :=
  inferInstanceAs (AddCommGroup (Cech.Hdeg _ _ _ _))
instance (i : ℕ) (c : ℤ) : Module S (laurentCohom S N i c) :=
  inferInstanceAs (Module S (Cech.Hdeg _ _ _ _))

def expToInt (e : Fin (N + 1) →₀ ℕ) : Fin (N + 1) → ℤ := fun j => (e j : ℤ)

def polyToLaurent : Poly S N →ₗ[S] Laurent S N where
  toFun p := Finsupp.mapDomain (expToInt N) (AddMonoidAlgebra.coeff p)
  map_add' p q := by
    change Finsupp.mapDomain _ (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q) = _
    exact Finsupp.mapDomain_add
  map_smul' r p := by
    change Finsupp.mapDomain _ (r • AddMonoidAlgebra.coeff p) = _
    exact Finsupp.mapDomain_smul r _

end Laurent

def SerrePoly.Laurent.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ),
    Function.Injective (polyToLaurent S N) ∧
    (∀ c : ℤ, ((polyGraded (S := S) (N := N)).piece c).map (polyToLaurent S N) =
      Finsupp.supported S S (laurentExps N c ∅)) ∧
    ∃ ι : ∀ I : StdCell N, LocMod S N (Poly S N) I.1 →ₗ[S] Laurent S N,
      (∀ I, Function.Injective (ι I)) ∧
      (∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1),
        ι J (locResS I J h z) = ι I z) ∧
      (∀ (I : StdCell N) (p : Poly S N), ι I (locMk (M := Poly S N) I.1 p) = polyToLaurent S N p) ∧
      ∀ (c : ℤ) (I : StdCell N),
        (degLoc (polyGraded (S := S) (N := N)) c I).map (ι I) = laurentDeg S N c I

def Cech.Transport.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R]
    (G : Cell U → Type v) [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    (G' : Cell U → Type w) [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
    (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J) (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J)
    (deg : ∀ I, Submodule R (G I)) (deg' : ∀ I, Submodule R (G' I)) (φ : ∀ I, G I →ₗ[R] G' I)
    (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (hdeg : ∀ I m, m ∈ deg I → φ I m ∈ deg' I),
    (∀ I, Function.Injective (φ I)) → (∀ I, (deg I).map (φ I) = deg' I) →
    ∀ i, Function.Bijective (Cech.mapHdeg deg deg' φ hφ hdeg i)

def Cech.Cone.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] (N : ℕ)
    (J : Finset (Fin (N + 1))),
    (∀ (W : Submodule R V) (i₀ : Fin (N + 1)), i₀ ∉ J → ∀ (i : ℕ)
      (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1)),
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) (i + 1) z = 0 →
      (∀ I, z I ∈ W) → (∀ I, ¬ J ⊆ I.1.1 → z I = 0) →
      ∃ y : Cech.Cochain (fun _ : StdCell N => V) i, (∀ I, y I ∈ W) ∧ (∀ I, ¬ J ⊆ I.1.1 → y I = 0) ∧
        Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i y = z) ∧
    (J.Nonempty → ∀ i₀ : Fin (N + 1), i₀ ∉ J → ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 →
      (∀ I, ¬ J ⊆ I.1.1 → z I = 0) → z = 0) ∧
    ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 → ∀ I K, z I = z K

def SerrePoly.LaurentCohom.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (laurentCohom S N i c)) ∧
    (∀ c : ℤ, 0 ≤ c → ∀ i, 1 ≤ i → Subsingleton (laurentCohom S N i c)) ∧
    ∀ c : ℤ, 0 ≤ c → ∀ z : Cech.Cochain (fun _ : StdCell N => Laurent S N) 0,
      z ∈ Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
        (Cech.idRes S (Laurent S N) Finset.univ) 0 →
      ∃ f ∈ Finsupp.supported S S (laurentExps N c ∅), ∀ I, z I = f

section Hypotheses

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistSplit.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (G B : SubSystem S x Ω) (r : ℕ)
    (η : Fin (r + 1) → Ω), (∀ I, M₀.tilde 0 I = G.sub I) →
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ (M : Type w) (_ : AddCommGroup M) (_ : Module (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (_ : Module (MvPolynomial (Fin (r + 1)) S) M)
      (_ : IsScalarTower (MvPolynomial (Fin (r + 1)) S) (Poly (MvPolynomial (Fin (r + 1)) S) N) M)
      (𝓜 : GradedPMod (MvPolynomial (Fin (r + 1)) S) N M),
      Module.Finite (Poly (MvPolynomial (Fin (r + 1)) S) N) M ∧
      ∀ (b : ℕ) (c : ℤ) (i : ℕ),
        ∃ (ι : ((G.twist (B.pow b)).twist (twistSys S x c)).H i →+ cohom 𝓜 i c)
          (π : cohom 𝓜 i c →+ ((G.twist (B.pow b)).twist (twistSys S x c)).H i), ∀ z, π (ι z) = z

section Hypotheses

variable (k : Type u) [Field k] (N : ℕ)

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (Nf : Fin (n + 1) → FinGradedSub (S := S) (x := x) E) (g : Fin n → E) (deg : Fin n → ℤ)
      (pr : Fin n → Ideal (Poly S N)),
      Nf 0 = M₂ ∧ Nf (Fin.last n) = M₁ ∧
      ∀ k : Fin n, (pr k).IsPrime ∧ (∀ p ∈ pr k, ∀ d : ℕ, homogeneousComponent d p ∈ pr k) ∧
        primeOf (S := S) x ≤ pr k ∧
        (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr k) ∧
        g k ∈ (Nf k.succ).piece (deg k) ∧
        (∀ c, (Nf k.succ).piece c = (Nf k.castSucc).piece c ⊔ Submodule.span S
          {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ deg k + d = c ∧ z = aeval x f • g k}) ∧
        ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d →
          (f ∈ pr k ↔ aeval x f • g k ∈ (Nf k.castSucc).piece (deg k + d))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def SubFamilyTwistPow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : SubFamily S x Ω) (a : ℕ),
    ∃ G : SubFamily S x E, G.toSubSystem = F.twist (Q.pow a)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SubFamilyTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : LineBundle S x), (∀ I, (F.sub I).FG) →
    ∃ G : SubFamily S x E, G.toSubSystem = F.toSubSystem.twist Q.toSubSystem ∧ ∀ I, (G.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
end
