module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle004
import GroundTheory.LocalFields.UnramifiedHensel
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle017
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef

@[expose] public section

section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W
def TwAwayAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ)
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (R : _root_.Formalism.ConjugateSelfDual.G K Ω →* GL (Fin n) (Qbar l)), Continuous R →
    ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ) (μ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → Continuous μ →
    IsLAdicOf art ι κ m μ → ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal →
    ∀ τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K)), Good (IrrGL.of τ.ρ τ.smooth τ.irred) →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) →
    ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc →
      IsWDOf ι R (rc (algNorm τ)) → IsWDOf ι (tw R μ) (rc (algNorm τ'))
def SphUntwAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) (κ : HChar K)
    (w : HeightOneSpectrum (𝓞 K)) (τ τ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w τ'.ρ B →
    Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) → Good (IrrGL.of τ.ρ τ.smooth τ.irred) ∧
    ∀ (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion K) → WD h), IsRecT h rc → Gd (rc (algNorm τ))
def PsFullAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (hh : Fin n → (L →+* Qbar l) → ℤ) (ψ : Fin n → _root_.ReciprocityTheory.Gal.Dec (F := L) A →* (Qbar l)ˣ)
    (ph : Fin n → Ine (F := L) A →* (Qbar l)ˣ), IsSubquotient τ.ρ (Hi.PS ω) → (∀ i, Hi.OrdChar ι a (ω i) (hh i) (ψ i)) →
    (∀ j, V.W.IsWtPart h (ψ j) (fun e => hh j (e.1.comp (algebraMap L (w.adicCompletion L)))) (ph j)) → Function.Injective ph →
    Nonempty (τ.ρ.Equiv (Hi.PS ω))
end UpperTheory.V.Z.Desc.W
end
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem lc_adic {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : Alg.AdicCont (maximalIdeal R) a) : Alg.AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
private theorem lc_chi {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : W.GDet n R G) (f : R →+* R') (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f ∧
      ∀ i, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at h
private theorem lc_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (Hi.heckePol n q a).map f = Hi.heckePol n q fun j => f (a j) := by

  simp [Hi.heckePol, Polynomial.map_sum]
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {T' T : Type} [CommRing T'] [CommRing T] [Algebra c.O T'] [Algebra c.O T]
    (Φ : T' →ₐ[c.O] T) (v : H.V) (g : Dec (F := L) (H.pl v))
private theorem lc_eps (p : T'ˣ) (i : ℕ) :
    (Units.map Φ.toRingHom.toMonoidHom p * H.epsV T v g ^ i : Tˣ) = Units.map Φ.toRingHom.toMonoidHom (p * H.epsV T' v g ^ i) := by
  rw [map_mul, map_pow]
  congr 2
  exact Units.ext (Φ.commutes _).symm
private theorem lc_unit (p : Dec (F := L) (H.pl v) →* T'ˣ) (i : ℕ) (b' : T') (b : T) (hb : Φ b' = b)
    (h : (p g * H.epsV T' v g ^ i : T'ˣ) * b' = 1) : (W.pushCh Φ.toRingHom p g * H.epsV T v g ^ i : Tˣ) * b = 1 := by
  have e := congrArg Φ h
  rw [map_mul, map_one, hb] at e
  rw [← e]
  exact congrArg (fun u : Tˣ => (u : T) * b) (lc_eps H Φ v g (p g) i)
private theorem lc_unif (p : Fin n → Dec (F := L) (H.pl v) →* T'ˣ) (j : Fin n) (b' : T') (b : T) (hb : Φ b' = b)
    (h : ((∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ) : T'ˣ) : T') = b') :
    ((∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = b := by
  rw [← hb, ← h]
  have e : (∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) =
      Units.map Φ.toRingHom.toMonoidHom (∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => lc_eps H Φ v g (p i g) i
  rw [e]
  rfl
end
private theorem lc_cont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (D : W.GDet n R G) (h : D.IsCont (maximalIdeal R)) : (D.map f.toRingHom).IsCont (maximalIdeal R') := fun i => by
  rw [funext fun g => (lc_chi D f.toRingHom g).2 i]
  exact lc_adic f (h i)
private theorem lc_pcont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {G : Type} [Group G] [TopologicalSpace G]
    (p : G →* Rˣ) (h : Alg.AdicCont (maximalIdeal R) fun g => (p g : R)) :
    Alg.AdicCont (maximalIdeal R') fun g => (W.pushCh f.toRingHom p g : R') :=
  lc_adic f h
private theorem lc_frob {O : Type} [CommRing O] {R R' : Type} [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G]
    (D : W.GDet n R G) (g : G) (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ∀ j, P j → R) (b' : ∀ j, P j → R')
    (hb : ∀ j h, f (b j h) = b' j h)
    (h : D.chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b j h else 1) :
    (D.map f.toRingHom).chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b' j h else 1 := by
  rw [(lc_chi D f.toRingHom _).1, h, lc_pol]
  refine congrArg _ (funext fun j => ?_)
  split_ifs
  · exact hb _ _
  · exact map_one _
private theorem lc_comp {O : Type} [CommRing O] {R T' T : Type} [CommRing R] [Algebra O R] [CommRing T'] [Algebra O T']
    [CommRing T] [Algebra O T] (f' : R →ₐ[O] T') (Φ : T' →ₐ[O] T) (f : R →ₐ[O] T) {n : ℕ} {G V : Type} {Γ : V → Type} [Group G]
    [∀ v, Group (Γ v)] (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (hu : ∀ f g : R →ₐ[O] T, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : D.map f.toRingHom = (D.map f'.toRingHom).map Φ.toRingHom ∧
      (fun v i => W.pushCh f.toRingHom (ψ v i)) = fun v i => W.pushCh Φ.toRingHom (W.pushCh f'.toRingHom (ψ v i))) (t : R) :
    f t = Φ (f' t) := by
  rw [hu f (Φ.comp f') (h.1.trans ((CA.d_gmap D).2.1 _ _)) fun v i => congrFun (congrFun h.2 v) i]
  rfl

private theorem lc_univ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K)
    (hΦg : ∀ i, Φ (H.gen θ a K' i) = H.gen θ a K i) (hΦA : ∀ b, Φ (algebraMap A _ b) = algebraMap A _ b)
    (D : W.GDet n (H.TK θ a K') H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K')ˣ)
    (hU : H.IsUniv θ a K' (maximalIdeal _) D ψ) :
    H.IsUniv θ a K (maximalIdeal _) (D.map Φ.toRingHom) fun v i => W.pushCh Φ.toRingHom (ψ v i) := by
  refine { cont := lc_cont Φ D hU.cont, ψ_cont := ?_, frob := ?_, ψ_unit := ?_, ψ_unif := ?_ }
  · intro v i
    exact lc_pcont Φ (ψ v i) (hU.ψ_cont v i)
  · intro w B σ hB hσ
    exact lc_frob Φ D _ _ (fun j => 0 < j ∧ j - 1 < n) _ _ (fun _ _ => hΦg _) (hU.frob w B σ hB hσ)
  · intro v i s g u hg hs
    exact lc_unit H Φ v g (ψ v i) i _ _ (hΦA _) (hU.ψ_unit v i s g u hg hs)
  · intro v j s g hg hs
    exact lc_unif H Φ v g (ψ v) j _ _ (hΦg _) (hU.ψ_unif v j s g hg hs)
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.level_change_compat_rank_two_of_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → ∀ (f : R →ₐ[c.O] H.TK θ a K) (f' : R →ₐ[c.O] H.TK θ a K'), H.IsMap θ a K D₀ ψ₀ f → H.IsMap θ a K' D₀ ψ₀ f' → ∀ φ : H.MK θ a K →ₗ[A] H.MK θ a K', Function.Injective φ → (∀ i (y : H.MK θ a K), ((φ ((H.gen θ a K i : Module.End A (H.MK θ a K)) y) : H.MK θ a K') : H.X.Fn A H.m) = H.op A i (φ y)) → ∀ t y, φ ((f t : Module.End A (H.MK θ a K)) y) = (f' t : Module.End A (H.MK θ a K')) (φ y) := by
  intro _ L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ _ a K K' _ _ _ _ R _ _ D₀ ψ₀ huniq f f' hf hf' φ hφ hgen t y
  obtain ⟨Ψ, hΨg, hΨ⟩ := levelUR2HeckeMap A _ _ _ _ (H.MK θ a K) (H.MK θ a K') (H.op A) (H.op A) φ id hφ hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K, ∀ x, Φ x = Ψ x := ⟨Ψ.restrictScalars c.O, fun _ => rfl⟩
  have hM := lc_univ H θ a K K' Φ (fun i => (hΦ _).trans (hΨg i)) (fun b => (hΦ _).trans (Ψ.commutes b)) _ _ hf'
  have hcore (D D' : W.GDet n (H.TK θ a K) H.Gq)
      (ψ ψ' : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ)
      (hU : H.IsUniv θ a K (maximalIdeal _) D ψ)
      (hU' : H.IsUniv θ a K (maximalIdeal _) D' ψ') : D' = D ∧ ψ' = ψ := by
    have adic_ext {Γ : Type} [TopologicalSpace Γ] {S : Set Γ} (hS : Dense S)
        {p q : Γ → H.TK θ a K} (hp : Alg.AdicCont (maximalIdeal _) p)
        (hq : Alg.AdicCont (maximalIdeal _) q) (hpq : ∀ x ∈ S, p x = q x) : p = q := by
      funext x
      refine IsHausdorff.eq_iff_smodEq (I := maximalIdeal (H.TK θ a K)).2 fun N => ?_
      rw [smul_eq_mul, Ideal.mul_top]
      let : TopologicalSpace (H.TK θ a K ⧸ maximalIdeal (H.TK θ a K) ^ N) := ⊥
      have : DiscreteTopology (H.TK θ a K ⧸ maximalIdeal (H.TK θ a K) ^ N) := ⟨rfl⟩
      exact congrFun (Continuous.ext_on hS (hp N).continuous (hq N).continuous
        fun z hz => by simp only [hpq z hz]) x
    refine ⟨CA.d_gext D' D fun g i _ _ => congrFun (adic_ext hA.dense (hU'.cont i) (hU.cont i) ?_) g, ?_⟩
    · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      simp only [W.GDet.lam, hU.frob ⟨w, hw⟩ B σ hB hσ, hU'.frob ⟨w, hw⟩ B σ hB hσ]
    · funext v i
      have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec (H.ovr v))) :=
        UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (H.ovr v)
      refine MonoidHom.ext fun g =>
        Units.ext (congrFun (adic_ext hd (hU'.ψ_cont v i) (hU.ψ_cont v i) ?_) g)
      rintro _ ⟨s, rfl⟩
      let incl := Subgroup.inclusion (Weil_le_Dec (H.ovr v))
      let p := (ψ' v i).comp incl
      let q := (ψ v i).comp incl
      have unit_eq (s₀ : Weil (H.ovr v)) (u : Uo ((H.Sl v).adicCompletion L))
          (hu : H.art v s₀ = u) : p s₀ = q s₀ := by
        have e := hU'.ψ_unit v i s₀ (incl s₀) u rfl hu
        have e' := hU.ψ_unit v i s₀ (incl s₀) u rfl hu
        exact mul_right_cancel (inv_injective (Units.ext
          ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
      have unif_eq (s₀ : Weil (H.ovr v)) (hu : H.art v s₀ = unif _) : p s₀ = q s₀ := by
        let pε := fun j : Fin n => ψ' v j (incl s₀) * H.epsV (H.TK θ a K) v (incl s₀) ^ (j : ℕ)
        let qε := fun j : Fin n => ψ v j (incl s₀) * H.epsV (H.TK θ a K) v (incl s₀) ^ (j : ℕ)
        have prod_eq (j : Fin n) : ∏ k with k ≤ j, pε k = ∏ k with k ≤ j, qε k :=
          Units.ext ((hU'.ψ_unif v j s₀ (incl s₀) rfl hu).trans
            (hU.ψ_unif v j s₀ (incl s₀) rfl hu).symm)
        have term_eq (j : Fin n) : pε j = qε j := by
          induction j using WellFoundedLT.induction with
          | ind j ih =>
            have hj : j ∈ Finset.univ.filter fun k => k ≤ j :=
              Finset.mem_filter.2 ⟨Finset.mem_univ j, le_rfl⟩
            have e := prod_eq j
            rw [← Finset.mul_prod_erase _ pε hj, ← Finset.mul_prod_erase _ qε hj,
              Finset.prod_congr rfl (g := qε) fun k hk => ih k (by
                rw [Finset.mem_erase, Finset.mem_filter] at hk
                exact lt_of_le_of_ne hk.2.2 hk.1)] at e
            exact mul_right_cancel e
        exact mul_right_cancel (term_eq i)
      obtain ⟨s₀, hs₀⟩ := (hA.art_spec v).surj (unif _)
      have e := unit_eq (s * (s₀ ^ ord _ (H.art v s))⁻¹) ⟨_, GlAx.val_div_ord (H.art v s)⟩ (by
        rw [map_mul, map_inv, map_zpow, hs₀]
        exact (div_eq_mul_inv _ _).symm)
      rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, unif_eq s₀ hs₀] at e
      exact congrArg Units.val (mul_right_cancel e)
  have e := lc_comp f' Φ f D₀ ψ₀ (huniq _) (hcore _ _ _ _ hM hf) t
  rw [e, hΦ]
  exact hΨ (f' t) y
end
end

section




section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem torusChar_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {a b : Fin n → kˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  funext i
  ext x
  have e := DFunLike.congr_fun h (Pi.mulSingle i x)
  simp only [torusChar_apply] at e
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (fun h => (h (Finset.mem_univ i)).elim),
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (fun h => (h (Finset.mem_univ i)).elim)] at e
  simpa using congrArg Units.val e
private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) :=
    ValuativeRel.ValueGroupWithZero.mk_pos.2 (ValuativeRel.zero_vlt_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)
private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) :=
      ValuativeRel.ValueGroupWithZero.mk_pos.2 (ValuativeRel.zero_vlt_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _
theorem UpperTheory.V.Z.Sym.Al.subquotient_prin_series_of_iwahori_eigenvector :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
        IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ ((Sig.Lev.iw k).J n) →
        (∀ d, Sig.SDom d → Hi.dc τ ((Sig.Lev.iw k).J n) ((Sig.Lev.iw k).J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ) := by
  intro H k _ _ _ _ n ψ T _ _ τ hs hi v hv0 hvJ heig
  have hJ : (Sig.Lev.iw k).J n = UpperTheory.V.AlgebraTools.iwC k n ⊤ := (UpperTheory.V.Z.Sym.Sig.link k n).1
  rw [hJ] at hvJ heig
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.thetaEx k n ⊤ ℂ T τ hq
  let δ : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar ψ * δ⁻¹
  let w : Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤) := ⟨v, hvJ⟩
  have hw0 : w ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hsd : ∀ d, Sig.SDom d →
      (θ d : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ d : ℂ) • w := by
    intro d hd
    have hD : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
      rcases hij.eq_or_lt with rfl | h
      · exact le_rfl
      · exact (hd i j h).le
    rw [hθ d hD]
    refine Subtype.ext ?_
    have h1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ _ _ (Sig.dg d)
      ((UpperTheory.V.AlgebraTools.heckePairIwC k n ⊤).1 (Sig.dg d))).1 w
    exact h1.trans (heig d hd)
  have ht : ∀ t, (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ t : ℂ) • w := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Units.val_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_right_injective _ (Units.ne_zero (χ d)) h2
  have hne : (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) (χ t : ℂ)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨w, (Submodule.mem_iInf _).2 fun t => ?_, hw0⟩
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [ht t]
  obtain ⟨ψ', -, -, e, h2⟩ := UpperTheory.V.AlgebraTools.jqEmbed H.loc.bz k n ⊤ T τ hs hi θ hθ χ hne
  have hψ : ψ' = ψ := torusChar_injective (e.trans (by
    change torusChar ψ * δ⁻¹ * δ = torusChar ψ
    simp))
  exact hψ ▸ h2
end
end

section




section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
def Step_cuspSupp_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (X : Type)
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) k) X), IsSmooth σ → σ.IsIrreducible →
    ∀ η : kˣ →* ℂˣ, IsSmoothChar η → HasDetVec σ η →
      ∃ μ : Fin d → kˣ →* ℂˣ, (∀ j, IsSmoothChar (μ j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ j u = η u) ∧
        IsCuspSupport σ (fun _ => 1) (fun j => detRep (Fin 1) (μ j))
def Step_prodIrr_alt : Prop :=
  _root_.UpperTheory.TNZ.Step_cuspSupp_alt → _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s N : ℕ) (d : Fin s → ℕ)
    (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (σ : ∀ b, Representation ℂ (GL (Fin (d b)) k) (X b)), (∀ b, IsSmooth (σ b)) → (∀ b, (σ b).IsIrreducible) →
    ∀ η : Fin s → kˣ →* ℂˣ, (∀ b, IsSmoothChar (η b)) → (∀ b, HasDetVec (σ b) (η b)) →
    (∀ b c, b ≠ c → ∃ u : kˣ, valuation k (u : k) = 1 ∧ η b u ≠ η c u) →
      (multiProd (stdBlocks d hd) σ).IsIrreducible
def GMainAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (ε : EpsFamily A) (rc : IrrGL (k := w.adicCompletion E) → WD h), Laws a ha ε rc → _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt →
    ∀ (s : ℕ) (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ), (∀ b, IsSmoothChar (η b)) →
    (∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t))) →
    ∀ (x : IrrGL (k := w.adicCompletion E)) (hd : ∑ b, d b = x.1),
      ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
          (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
        IsTwSphProd x.rep d hd η
end UpperTheory.TNZ
end
end
end

section




section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
namespace UpperTheory.V.Th
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
def RigPtAlt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka) →
      FreeAt l r → RigOver r ka
end
def RigPtOfAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O) (n : ℕ)
    (ka : G L Ω →* (Qbar l)ˣ) (_ : CReal k c₁ f n ka), W.Large L c₁ → IsKa σ M ι n ka → _root_.UpperTheory.V.Th.RigPtAlt k n ι ka
def LinkedRigAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ →
    SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    _root_.UpperTheory.V.Th.RigPtAlt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, IsKa σ M ι 2 ka ∧ _root_.UpperTheory.V.Th.RigPtAlt k 2 ι ka
end UpperTheory.V.Th
end
end
end
