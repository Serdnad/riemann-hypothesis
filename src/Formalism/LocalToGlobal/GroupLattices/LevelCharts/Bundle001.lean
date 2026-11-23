module

public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteCompG
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGGlob
public import Formalism.SharpRestriction.GrowthBounds.Bundle002
public import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}
    {Z : Type} [CommGroup Z]

theorem awayG_le_comap (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    awayG σE J Uloc p ≤ (Uloc v).comap (bc (prV (E := E) v)) :=
  fun x hx => ((mem_awayG σE J Uloc p x).1 hx).2 v hv


variable (σE J Uloc) in
def lamQG (Q : Finset (HeightOneSpectrum (𝓞 F))) (lamQ : ∀ v, v ∈ Q → (Uloc v →* Z)) (p : ℕ)
    (hQ : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) : awayG σE J Uloc p →* Z :=
  prodChar Q Uloc lamQ (awayG σE J Uloc p) (fun v hv => awayG_le_comap p v (hQ v hv))

end Formalism.L2.G
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat}

structure GChartTie {p : ℕ} {G : GAtP p} (X : Formalism.L2.Herm.GLevTie L G) {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {cmp : Type}
    (em : cmp → Lv.compS i) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (ψ : awayG sp.cm.sig J Uloc p →* G.Oˣ) (eps : UJ (sp.cm.sig : E →+* E) J →* G.Oˣ) where

  em_inj : Function.Injective em

  rk : (Fl.Pj (i + 1)).m + 1 = N

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (X.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : cmp → UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)
  yG_p : ∀ c (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1
  yG_bij : Function.Bijective (fun c : cmp => (Quotient.mk'' (yG c) : compG sp.cm.sig J Uloc p))

  gamI : ∀ c, (Lv.levS i (em c)).Γ →* UJ (sp.cm.sig : E →+* E) J
  gamI_inj : ∀ c, Function.Injective (gamI c)
  gamI_range : ∀ c (γ : UJ (sp.cm.sig : E →+* E) J), γ ∈ (gamI c).range ↔
    bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin N) E) ∈
      (awayG sp.cm.sig J Uloc p).map (MulAut.conj (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).toMonoidHom

  act_eq : ∀ c (v : Fin G.P.nV) w (h : (X.pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (Lv.levS i (em c)).Γ)
    (a b : Fin ((Fl.Pj (i + 1)).m + 1)) (a' b' : Fin N), (a : ℕ) = a' → (b : ℕ) = b' →
    X.eQ v w h (((Lv.levS i (em c)).act v γ : GL (Fin ((Fl.Pj (i + 1)).m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (X.spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI c γ : GL (Fin N) E)) * fr w hw :
          GL (Fin N) (w.adicCompletion F)) : Matrix (Fin N) (Fin N) (w.adicCompletion F)) a' b'

  chi_eq : ∀ c (γ : (Lv.levS i (em c)).Γ) (x : awayG sp.cm.sig J Uloc p),
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      (yG c : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))⁻¹ *
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamI c γ : GL (Fin N) E) * yG c →
    (Lv.levS i (em c)).χ γ = ψ x * eps (gamI c γ)

variable {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}


def ChartsCover {p : ℕ} {G : GAtP p} {Fl : Fills G} (Lv : Levels Fl) (i : ℕ) {Cb : Type} {cmp : Cb → Type}
    (em : ∀ β, cmp β → Lv.compS i) : Prop :=
  Function.Bijective (fun x : Σ β, cmp β => em x.1 x.2)

end Formalism.L2.G
end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

structure FrS (I : LocId L p nV W Qq) {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)) where
  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin N) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin N → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w Lb, ∀ a, (I.spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin N) (w.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

def FrS.frQ {I : LocId L p nV W Qq} {N : ℕ} {Lb : Submodule (𝓞 E) (Fin N → E)} (B : FrS I Lb) (v : Fin nV) :
    GL (Fin N) Qq := bc (I.eQ v).symm.toRingHom (B.fr (I.pl v).1 (I.pl v).2)

structure StepAt (I : LocId L p nV W Qq) (O : Type) [CommRing O] (N : ℕ) where
  J : Matrix (Fin N) (Fin N) E
  Lb : Submodule (𝓞 E) (Fin N → E)
  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))
  fr : FrS I Lb
  ψ : awayG sp.cm.sig J Uloc p →* Oˣ

  eps : UJ (sp.cm.sig : E →+* E) J →* Oˣ
  fin : Finite (compG sp.cm.sig J Uloc p)

namespace StepAt

variable {I : LocId L p nV W Qq} {O : Type} [CommRing O] {N : ℕ} (St : StepAt I O N)

abbrev Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := awayG sp.cm.sig St.J St.Uloc p

abbrev comp : Type := compG sp.cm.sig St.J St.Uloc p

abbrev rep (i : St.comp) : UPts sp.cm.sig St.J (FiniteAdeleRing (𝓞 F) F) := repG sp.cm.sig St.J St.Uloc p i

end StepAt

variable {n' : ℕ} {O Kf : Type} [IsDomain W] [IsDiscreteValuationRing W]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev levStep (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) {m' : ℕ} (lam' : Fin nV → Fin n' → Fin (m' + 1) → ℤ)
    (dom' : ∀ v, IsDominant (lam' v)) {N : ℕ} (hk : m' + 1 = N) {I : LocId L p nV W Qq} (St : StepAt I O N) (i : St.comp) :
    Level (placesConst hS nV m' r lam' dom') :=
  { levC sp.cm.sig St.J St.Up hS nV r lam' dom' hk I.iw St.fr.frQ St.ψ
      (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) with
    χ := St.ψ.comp (gamToUp sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) *
      St.eps.comp (gamC sp.cm.sig St.J St.Up (St.rep i : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))).subtype }

abbrev levelsOf (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (St : ∀ i, i < M → StepAt I O (Nj i)) : Levels Fl where
  compS := fun i => (h : i < M) ×' (St i h).comp
  finS := fun i => by
    haveI : ∀ h : i < M, Finite (St i h).comp := fun h => (St i h).fin
    exact Fintype.ofFinite _
  levS := fun i c => levStep hS r (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1))
    (hN i c.1) (St i c.1) c.2

abbrev levelsOfCh (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (Fl : Fills (gatOfLevel L hS nV r lam0 dom hk I ψ y e)) (M : ℕ) (Nj : ℕ → ℕ)
    (hN : ∀ i, i < M → m + (i + 1) * (Fl.t + 1) + 1 = Nj i) (Ch : ∀ i, i < M → Type) [∀ i h, Finite (Ch i h)]
    (St : ∀ i (h : i < M), Ch i h → StepAt I O (Nj i)) : Levels Fl where
  compS := fun i => (h : i < M) ×' Σ b : Ch i h, (St i h b).comp
  finS := fun i => by
    haveI : ∀ (h : i < M) (b : Ch i h), Finite (St i h b).comp := fun h b => (St i h b).fin
    exact Fintype.ofFinite _
  levS := fun i c => levStep hS r (fun v s => liftWt Fl.t m (lam0 v s) (fun a => Fl.w v a s) (i + 1)) (Fl.domJ (i + 1))
    (hN i c.1) (St i c.1 c.2.1) c.2.2

end Formalism.L2.G
end
end
