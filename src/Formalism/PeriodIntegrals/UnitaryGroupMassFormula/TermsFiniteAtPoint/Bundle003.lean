module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
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

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

def LoB {E : Type} [Field E] [NumberField E] {N : ℕ} (b : 𝓞 E) (A : Matrix (Fin N) (Fin N) (𝓞 E)) : Prop :=
  ∀ i j, (i < j → A i j = 0) ∧ (i = j → A i j = 1) ∧ (j < i → b ∣ A i j)

def UpB {E : Type} [Field E] [NumberField E] {N : ℕ} (b : 𝓞 E) (B : Matrix (Fin N) (Fin N) (𝓞 E)) : Prop :=
  ∀ i j, (j < i → B i j = 0) ∧ (i = j → B i j = 1) ∧ (i < j → b ∣ B i j)

def CellReduce : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) (p : Point E N) (b : 𝓞 E), b ≠ 0 →
    ∃ Zs : Set (Matrix (Fin N) (Fin N) E), Zs.Finite ∧
      ∀ Z : Matrix (Fin N) (Fin N) E, (∀ i j, ∃ o : 𝓞 E, (o : E) = Z i j) → IsInCell Z p →
        ∃ A B : Matrix (Fin N) (Fin N) (𝓞 E), LoB b A ∧ UpB b B ∧
          A.map (fun x => (x : E)) * Z * B.map (fun x => (x : E)) ∈ Zs

def heisFun {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (e a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E) (v : S.V) : S.V :=
  v + ∑ c, S.hT (e c) v • a c - ∑ c, S.hT (a c) v • e c + ∑ c, ∑ d, (s c d * S.hT (e d) v) • e c

def HeisOp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (a : Fin r → S.V) (s : Matrix (Fin r) (Fin r) E),
    (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 E, (o : E) = S.hT x y) →
    (∀ c, F.fl.e c ∈ Λ) → (∀ c, a c ∈ Λ) → (∀ c d, S.hT (F.fl.e c) (a d) = 0) →
    (∀ c d, ∃ o : 𝓞 E, (o : E) = s c d) →
    (∀ c d, s c d + star (s d c) = - S.hT (a c) (a d)) →
    ∃ n ∈ NLam Λ F, ∀ v, n v = heisFun F.fl.e a s v

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameOp : Prop :=
  ∀ (D : D7) (u : D.what₂.Word), ∃ b : ℕ, 0 < b ∧
    ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
      IsRowLat D F0 Λ → ∀ B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
        UpB (b : 𝓞 D.host.E) B →
        ∃ n ∈ NLam Λ (lf D F0), ∀ j,
          n (frame (lf D F0) j) = ∑ c, ((B c j : 𝓞 D.host.E) : D.host.E) • frame (lf D F0) c

def CarrierRow : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
    ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' →
      IsRowLat D F'.fl Λ ∧ lf D F'.fl = F'

def ShortFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (Λ : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E Λ → ∀ P : Submodule E S.V,
    (∀ x ∈ P, x ≠ 0 → ∀ τ : E →+* ℂ, 0 < (τ (S.hT x x)).re) → ∀ c : E,
      {x | x ∈ Λ ∧ x ∈ P ∧ S.hT x x = c}.Finite

end PI.TermsAtPtFiniteW
end
end

section

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AtSet (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Point D.host.E (D.R.rS + 1)) :
    Set (Carrier (PD D Λ (lf D F0) u')) :=
  {x | Gval (lf D F0) x.1 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D F0) x.1)) w}

def ZhatReduce : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word), (VS D).SigOK →
    ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
      IsRowLat D F0 Λ → ∀ w : Point D.host.E (D.R.rS + 1),
        ∃ Zs : Set (Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Zs.Finite ∧
          ∀ x ∈ AtSet D u u' F0 Λ w, ∃ y : Carrier (PD D Λ (lf D F0) u'),
            mk Λ (lf D F0) (PD D Λ (lf D F0) u') x = mk Λ (lf D F0) (PD D Λ (lf D F0) u') y ∧
              Gval (lf D F0) y.1 ≠ 0 ∧ ZhatL (lf D F0) y.1 ∈ Zs

def FixedZhatFinite : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word), (VS D).SigOK →
    ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
      IsRowLat D F0 Λ → ∀ Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
        (mk Λ (lf D F0) (PD D Λ (lf D F0) u') ''
          {y | Gval (lf D F0) y.1 ≠ 0 ∧ ZhatL (lf D F0) y.1 = Z}).Finite

theorem atPt_set_eq (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Point D.host.E (D.R.rS + 1)) :
    {t : TermsOf D u' F0 Λ | AtPt Λ (lf D F0) (PD D Λ (lf D F0) u') t w} =
      mk Λ (lf D F0) (PD D Λ (lf D F0) u') '' AtSet D u u' F0 Λ w := by
  ext t
  constructor
  · rintro ⟨F', ⟨h, hmk⟩, hG, hc⟩
    exact ⟨⟨F', h⟩, ⟨hG, hc⟩, hmk⟩
  · rintro ⟨x, ⟨hG, hc⟩, rfl⟩
    exact ⟨x.1, ⟨x.2, rfl⟩, hG, hc⟩

theorem termsAtFinite_of (hR : ZhatReduce) (hF : FixedZhatFinite) (D : D7) (u u' : D.what₂.Word) :
    TermsAtFinite D u u' := by
  intro hsig F0 Λ hΛ w
  obtain ⟨Zs, hZs, hred⟩ := hR D u u' hsig F0 Λ hΛ w
  rw [atPt_set_eq]
  refine (hZs.biUnion fun Z _ => hF D u u' hsig F0 Λ hΛ Z).subset ?_
  rintro t ⟨x, hx, rfl⟩
  obtain ⟨y, hxy, hG, hZ⟩ := hred x hx
  exact Set.mem_biUnion hZ ⟨y, ⟨hG, rfl⟩, hxy.symm⟩

end PI.TermsAtPtFiniteW
end
end
