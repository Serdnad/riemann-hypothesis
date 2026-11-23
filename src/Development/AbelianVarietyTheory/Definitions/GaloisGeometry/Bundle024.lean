module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle023
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.Row9

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E]

def FieldOK (l : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → IsSplitAt w) ∧
    ∃ w₁ w₂ w₃ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₁.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ w₂.asIdeal ∧
      ((l : ℕ) : 𝓞 E) ∈ w₃.asIdeal ∧ Apart w₁ w₂ ∧ Apart w₁ w₃ ∧ Apart w₂ w₃

def SatU {a : ℕ} (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  IsSplitAt w ∧ ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SphG (c : GlobalTheory.RoadU.Sph) {l : ℕ} [Fact l.Prime] {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (inf : (E →+* ℂ) → Multiset ℂ) : Prop :=
  match c with
  | .unr => ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = (inf (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O), Pst.Induces Bw →
      IsCrysAt P Bw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)
  | .phi => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g

def CoreUFor (m : ℕ) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), FieldOK l E →
    ∀ U : Submodule ℂ (UA E m → ℂ), IsAutRepU U → ∀ lam : (E →+* ℂ) → DomWeight m, (∀ τ, HasWeightAt U τ (lam τ)) →
    ∃ r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
      ∀ w B, SatU U w B → ∀ c, SphG c ι r w B fun τ => infOfWeight (lam τ)

def CoreU : Prop := ∀ m : ℕ, Odd m → CoreUFor m

def HalfIntegral {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (α : CG K 1) : Prop :=
  ∀ τ, ∀ z ∈ α.infChar τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

namespace Basic

section Sum

variable {Γ K : Type} [Group Γ] [Field K] {n k : ℕ} (r : Γ →* GL (Fin n) K) (ν : Fin k → (Γ →* Kˣ))

end Sum

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]

end Basic

end GlobalTheory.Row9

end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def PhiAt (ι : Qbar l ≃+* ℂ) (r : _root_.Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (_root_.ReciprocityTheory.Gal.Dec (F := E) A) O) (hBw : Pst.Induces Bw),
    ∀ (σ : Weil hA) (n : ℕ), GlobalTheory.CongPhi.phiSum (wdAt P ι Bw hA hBw (r.comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype)) σ n =
      GlobalTheory.CongPhi.phiSum (GlobalTheory.RoadU.satWD hA a B) σ n

def HasLevelOff (w₀ v' : HeightOneSpectrum (𝓞 E)) (Kw : Levels E a) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
    IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → GlobalTheory.PRep.fixed σ.ρ (Kw w) ≠ ⊥


open Classical in
def PowSatU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (n : ℤ) : ℂ :=
  if h : ∃ B, SatU U w B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (fun z => z ^ n)).sum else 0

end GlobalTheory.CongL

end
end

section

noncomputable section

namespace GlobalTheory.AtG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker
open scoped ComplexConjugate

def JetSplitAmb : Prop :=
  ∀ {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b))
      (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Even a → Even b → Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' →
      s.StdAtP p N → s.StdAtP p N' → ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p →
      ¬ p ∣ D.host.d → (ambOf s B χ cD : Amb X).LaHyp a b S →
      ∀ (π : ℂ) (pE : 𝓞 X.E), Formalism.L2.AlgTh.IsQInt D.host.d π → π * conj π = (p : ℂ) → Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE →
      ∀ (c' : ℕ) (x : Formalism.L2.Col.HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ Formalism.L2.Col.divLat c' (Formalism.L2.Col.homAt S N N') → ∀ m : DVar X.Tau a b →₀ ℕ,
        ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1


open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound in
def TiesAt (D : D7) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup) : Prop :=
  ∃ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : _) (eta : _) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _),
    HostTie EX ∧ CharTie Ch mu0 eta sel ∧ AnTie D δ χ cD ∧
      ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ


open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat in
def RowPin {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : ColIn.Ok I) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) : Prop :=
  ∀ u : B.Word, ∃ e : (I.per l u a).Mt ≃ₗ[ℂ] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Amb a,
    (a = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → HEq e ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMt u)) ∧ (a ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → e = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMtTw u a) ∧
    (∀ v ∈ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Amb a → 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL,
      e (rowForm I l h u a z) = ∑ v ∈ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Mtilde a).gen, (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.embLL ((c v : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL) • v

end GlobalTheory.AtG

end
end

section

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms _root_.Formalism.L2.Col Formalism.L2.DIV NumberField IsDedekindDomain

def stabSet {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)
    (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (q : UF X.E n → Prop) : Set (Matrix (Fin n) (Fin n) D.host.E × ℂ) :=
  {g | ∃ a : FrmG Λ Θ, a • p = p ∧ q a.1 ∧ g = (matE s a.1.1, s.σ₀ ((Λ.chr a.2.1 * Θ.chr a.2.2 : X.Kˣ) : X.K))}

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

def StabPin (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (G : StabDat (D.chTw u μ)) : Prop :=
  ∃ (pt : ∀ i, i ≤ t.m2 + 1 → (D.chTw u μ).cls i → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (ix : ∀ i, i ≤ t.m2 → (D.chTw u μ).cls i → (t.idx μ).β i)
    (yb : (D.chTw u μ).cls (t.m2 + 1) → Set (Sp t.X.E (D.R.N (t.m2 + 1))))
    (pT : (D.chTw u μ).cls (t.m2 + 1 + 1) → ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1 + 1)),
    (∀ i (hi : i ≤ t.m2 + 1) c, (t.rd u μ).N i c = (pt i hi c).deco.1.N) ∧
    (∀ c', yb c' ∈ ybSet t.sel (t.tup μ) (t.cst μ) (pt (t.m2 + 1) le_rfl c').deco.1.N) ∧
    (∀ i (hi : i < t.m2) c c' x, (t.rd u μ).Xi i c c' x = t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (ix i hi.le c)
      (ix (i + 1) hi c') (pt i (by omega) c) (pt (i + 1) (by omega) c') x)) ∧
    (∀ c c' x, (t.rd u μ).Xi t.m2 c c' x = t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (ix t.m2 le_rfl c)
      (pt t.m2 (Nat.le_succ _) c) (pt (t.m2 + 1) le_rfl c') (yb c') x)) ∧
    (t.rd u μ).TopPinAt t.Ch t.sel (t.tup μ) (t.cst μ) t.seam.σ₀ (t.word u) t.m2 (pt (t.m2 + 1) le_rfl) yb pT ∧
    (∀ i, 1 ≤ i → ∀ (hi : i ≤ t.m2) c, G i c = stabSet t.seam ((t.idx μ).levG i (ix i hi c)) ((t.idx μ).levQ i (ix i hi c))
      (pt i (Nat.le_succ_of_le hi) c) fun _ => True) ∧
    (∀ (b : (t.idx μ).β (t.m2 + 1)) c, G (t.m2 + 1) c = stabSet t.seam ((t.idx μ).levG (t.m2 + 1) b) ((t.idx μ).levQ (t.m2 + 1) b)
      (pt (t.m2 + 1) le_rfl c) fun γ => (fun v => γ.1 v) '' yb c = yb c) ∧
    ∀ c, G (t.m2 + 1 + 1) c = stabSet t.seam (twLt t.Ch (t.m2 + 1 + 1)) (twTt (R := D.R) t.sel (t.tup μ) (t.m2 + 1 + 1)) (pT c) fun _ => True

def FormsPin (t : KerEntTied ex) : Prop :=
  ∀ u μ, DV.Used D μ → ∃ G : StabDat (D.chTw u μ), FormsAre (ex.tw.fm u μ) (t.O u μ) G ∧ StabPin t u μ G

structure ColSide (t : KerEntTied ex) : Prop where
  fields : t.X.Ok
  sel : IsSel t.X t.sel
  bad : (∀ i, t.Pr.g i ∈ t.S) ∧ (∀ v, t.Pr.T v ∈ t.S) ∧ (∀ l ∈ D.host.small, l ∈ t.S) ∧ D.host.q ∈ t.S
  chOk : t.Ch.Ok
  chars : ∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta
  sharp : ∀ μ, (t.cst μ).sharp = true
  deep : ∀ μ, D.R.m ≤ (t.cst μ).A ∧ 2 * (t.cst μ).M ≤ twTopDepth D.R
  repOne : ∀ μ j, j ≤ t.m2 + 1 → ∀ (b : (t.idx μ).β j) (P : rowSG t.Pr t.sel (t.tup μ)), P.1 ∈ t.Pr.vGs → (t.idx μ).h j b P = 1

end GlobalTheory.KerJ
end
end
