module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Mathlib.GroupTheory.Coprod.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle302
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical

namespace GlobalTheory.LocWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def idem (D : D7) : Pl D → AE D
  | .inl v => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin D v
  | .inr τ => GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf D (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))

theorem idem_mul_self (v : Pl D) : idem D v * idem D v = idem D v := by
  rcases v with v | τ
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemFin]
    rw [← map_mul]
    congr 1
    refine Prod.ext (mul_zero _) ?_
    change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
    refine DFunLike.ext _ _ fun u => ?_
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F v 1) = evalV D.host.F u (singleV D.host.F v 1)
    rw [map_mul]
    by_cases h : u = v
    · subst h
      have : evalV D.host.F u (singleV D.host.F u 1) = 1 := RestrictedProduct.single_eq_same
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) u 1
      rw [this, mul_one]
    · have : evalV D.host.F u (singleV D.host.F v 1) = 0 := RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 h
      rw [this, mul_zero]
  · simp only [idem, GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.idemInf]
    rw [← map_mul]
    congr 1
    refine Prod.ext ?_ (mul_zero _)
    exact (Pi.single_mul (α := fun w : InfinitePlace D.host.F => w.Completion) _ 1 1).symm.trans (by rw [mul_one]; rfl)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  simp [cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem cA_idem (v : Pl D) : cA D (idem D v) = idem D v := by
  rcases v with v | τ <;> exact cA_algebraMap _

def cutGL {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) : GL (Fin n) R →* GL (Fin n) R :=
  let f : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun g => e • g + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun g h => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
        have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
          Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add] }
  Units.map f

theorem cutGL_val {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (g : GL (Fin n) R) :
    (cutGL he g).val = e • g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := rfl

theorem cutGL_mem {R : Type} [CommRing R] {n : ℕ} {e : R} (he : e * e = e) (c : R →+* R) (hc : c e = e)
    (J : Matrix (Fin n) (Fin n) R) {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ c J) : cutGL he g ∈ Formalism.UG.UJ c J := by
  have hg' : Formalism.UG.cT c g.val * J * g.val = J := hg
  show Formalism.UG.cT c (cutGL he g).val * J * (cutGL he g).val = J
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  have e1 : Formalism.UG.cT c (cutGL he g).val = e • Formalism.UG.cT c g.val + (1 - e) • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    simp only [cutGL_val, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hc, Matrix.one_apply, eq_comm (a := j)]
    split_ifs <;> simp
  rw [e1, cutGL_val]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one,
    Matrix.one_mul, he, h1, h2, mul_comm (1 - e) e, zero_smul, add_zero, zero_add, smul_add, hg']
  rw [← add_smul]; simp

def comp (V : HSp D) (v : Pl D) : GA D V →* GA D V :=
  ((cutGL (idem_mul_self v)).comp (matHom V)).codRestrict (HR (AF D.host.F) D.sp.cm.sig V.gram) fun g =>
    cutGL_mem (idem_mul_self v) (cA D) (cA_idem v) _ g.2

def GAt (V : HSp D) (v : Pl D) : Subgroup (GA D V) := (comp V v).range

def Gk (θ : InfF D) (V : HSp D) (A : CptF V) : Subgroup (GA D V) :=
  GfC V ⊔ Subgroup.closure {k | V.SigOK ∧ IsKinf θ V A k}

def KAt (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Subgroup (GA D V) := (Gk θ V A).map (comp V (.inr τ))

def OneP (V : HSp D) (τ : D.what₂.Tau) : Type :=
  {γ : Multiplicative ℝ →* GA D V // Continuous γ ∧ ∀ t, γ t ∈ GAt V (.inr τ)}

abbrev HAlg (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : Type :=
  MonoidAlgebra ℂ (Monoid.Coprod (KAt θ V A τ) (FreeMonoid (OneP V τ)))

def ofK (θ : InfF D) (V : HSp D) (A : CptF V) (τ : D.what₂.Tau) : KAt θ V A τ →* HAlg θ V A τ :=
  (MonoidAlgebra.of ℂ _).comp Monoid.Coprod.inl

def Hloc (θ : InfF D) (V : HSp D) (A : CptF V) : Pl D → Type
  | .inl v => GAt V (.inl v)
  | .inr τ => HAlg θ V A τ

instance (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Monoid (Hloc θ V A v)
  | .inl v => inferInstanceAs (Monoid (GAt V (.inl v)))
  | .inr τ => inferInstanceAs (Monoid (HAlg θ V A τ))

def loc (θ : InfF D) (V : HSp D) (A : CptF V) : ∀ v, Gk θ V A →* Hloc θ V A v
  | .inl v => (comp V (.inl v)).rangeRestrict.comp (Gk θ V A).subtype
  | .inr τ => (ofK θ V A τ).comp ((comp V (.inr τ)).subgroupMap (Gk θ V A))

def IsEvalAt (D : D7) (v : FinF D) (w : FinE D) (φ : AE D →+* v.adicCompletion (FF D)) : Prop :=
  (∀ a, φ (algebraMap (AF D.host.F) (AE D) a) = evalV D.host.F v (sndA D.host.F a)) ∧
    ∀ x : 𝓞 D.host.E, Valued.v (φ (incA D (x : D.host.E))) < 1 ↔ x ∈ w.asIdeal

structure SplitFrames (D : D7) where
  ev : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (AE D →+* v.adicCompletion (FF D))
  ev_spec : ∀ v w hv hw, IsEvalAt D v w (ev v w hv hw)
  ev_conj : ∀ v w w' hv hw hw', w' ≠ w → ∀ x, ev v w' hv hw' x = ev v w hv hw (cA D x)
  sc : ∀ (v : FinF D) (w : FinE D), Split D v → Over D w v → (v.adicCompletion (FF D))ˣ
  sc_spec : ∀ v w hv hw x, IntV v 0 (((sc v w hv hw)⁻¹ : (v.adicCompletion (FF D))ˣ) * x) ↔
    x ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {y | ∃ a ∈ D.host.AA, y = ev v w hv hw (incA D a)}
  fr : ∀ (V : HSp D) (v : FinF D) (w : FinE D), Split D v → Over D w v → GL (Fin V.rank) (v.adicCompletion (FF D))
  fr_spec : ∀ V v w hv hw y, (∀ i, IntV v 0 (((fr V v w hv hw)⁻¹).val.mulVec y i)) ↔
    y ∈ Submodule.span (v.adicCompletionIntegers (FF D)) {z | ∃ x ∈ L0c D V, z = fun i => ev v w hv hw (incA D (x i))}
  fr_dual : ∀ V v w w' hv hw hw', w' ≠ w →
    (fr V v w' hv hw').valᵀ * V.gram.map (fun a => ev v w hv hw (incA D a)) * (fr V v w hv hw).val = 1

def SplitFrames.gl (Fr : SplitFrames D) (V : HSp D) (v : FinF D) (w : FinE D) (hw : Over D w v) :
    GAt V (.inl v) →* GL (Fin V.rank) (v.adicCompletion (FF D)) :=
  if hv : Split D v then
    (MulAut.conj (Fr.fr V v w hv hw)⁻¹).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map (Fr.ev v w hv hw)).comp ((matHom V).comp (GAt V (.inl v)).subtype))
  else 1

variable {X : ThetaX D} {T : ThetaTied D X}

def Splitting (T : ThetaTied D X) (V W : HSp D) (χ χ' : X.Chr) : Prop :=
  ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank

structure PairData {Wl : WeilTied D X T} (K : KfinTied Wl) (θ : InfF D) (Fr : SplitFrames D) (V W : HSp D)
    (om : X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Type 1 where
  S : Pl D → Type
  [sA : ∀ v, AddCommGroup (S v)]
  [sM : ∀ v, Module ℂ (S v)]
  omL : X.Chr → X.Chr → ∀ v, Representation ℂ (Hloc θ V (K.cpt V) v × Hloc θ W (K.cpt W) v) (S v)
  vac : ∀ v, S v
  pure : (∀ v, S v) → X.Sch V W
  pure_span : Submodule.span ℂ {Φ | ∃ φ, Restr vac φ ∧ Φ = pure φ} = X.kfin V W
  pure_om : ∀ χ χ', Splitting T V W χ χ' → ∀ (g : Gk θ V (K.cpt V)) (h : Gk θ W (K.cpt W)) φ, Restr vac φ →
    om χ χ' ((g : GA D V), (h : GA D W)) (pure φ) = pure fun v => omL χ χ' v (loc θ V _ v g, loc θ W _ v h) (φ v)
  pure_mlin : ∀ φ v (c : ℂ) (x y : S v), Restr vac φ →
    pure (Function.update φ v (c • x + y)) = c • pure (Function.update φ v x) + pure (Function.update φ v y)
  linM : ∀ (v : FinF D) (w : FinE D), Over D w v →
    S (.inl v) →ₗ[ℂ] (Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ)
  linM_inj : ∀ v w (hw : Over D w v), Split D v → Function.Injective (linM v w hw)
  linM_eq : ∀ χ χ' v w (hw : Over D w v), Splitting T V W χ χ' → Split D v →
    ∀ g k : _, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ, linM v w hw (omL χ χ' (.inl v) (g, k) φ) = c • fun Xm : Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) =>
      linM v w hw φ (Units.val (Fr.gl V v w hw g)⁻¹ * Xm * (Units.val (Fr.gl W v w hw k)⁻¹).transpose)

attribute [instance] PairData.sA PairData.sM

end GlobalTheory.LocWeil

end
end

section

noncomputable section

namespace GlobalTheory.Mem.SStageInhab

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem ncard_primesOver_eq (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime) :
    ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E l).ncard := by
  symm
  apply Set.ncard_congr (fun v _ => v.asIdeal)
  · intro v hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl)) (by simpa using hl.ne_zero)
    refine hm.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ v.asIdeal)) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [Ideal.under, placesOver] using hv
  · intro a b _ _ h; exact HeightOneSpectrum.ext h
  · rintro P ⟨hP, hP'⟩
    have hmem : ((l:ℕ) : 𝓞 E) ∈ P := by
      have : (l:ℤ) ∈ P.under ℤ := by rw [← hP'.over]; exact Ideal.mem_span_singleton_self _
      simpa [Ideal.under] using this
    refine ⟨⟨P, hP, ?_⟩, hmem, rfl⟩
    rintro rfl
    exact hl.ne_zero (by simpa using hmem)

theorem conjF_ne_id (B : Base) : B.toPre.conjF ≠ AlgHom.id _ _ := by
  letI := B.host.cmStar
  intro h
  have h2 := B.sp.cm.deg2
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a => by
    have : B.toPre.conjF a = a := by rw [h]; rfl
    exact (B.sp.cm.fixed a).1 this
  have : Module.finrank B.host.F B.host.E = 1 := by
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap.symm] ; exact ⟨(algebraMap B.host.F B.host.E).injective, hs⟩
  omega

theorem exists_locAt_split_iff (B : Base) (h2 : Module.finrank B.host.F B.host.E = 2) (hne : B.toPre.conjF ≠ AlgHom.id _ _) (p) :
    ∃ L : Formalism.MainNotions.S.Loc.LocAt B.host.F B.host.E B.toPre.conjF p, (L.split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt _ _ B.toPre.conjF h2 p
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt _ _ _ h2 hne p L (by
      rw [ncard_primesOver_eq _ _ L.ellPrime.out]
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> rw [h] <;> exact B.toPre.g_split _)
    exact ⟨{L with split := some S}, by simp [h]⟩
  · exact ⟨L, by simp [hL, h]⟩

theorem nonempty_conj_embedding (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] (d D : ℕ) (h : d ≤ D)
    (b : OrthonormalBasis (Fin d) ℂ EE) : Nonempty (EE →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin D)) := by
  let e := EuclideanSpace.basisFun (Fin D) ℂ
  have ho : Orthonormal ℂ (fun i : Fin d => e (Fin.castLE h i)) := e.orthonormal.comp _ (Fin.castLE_injective h)
  let f : EE →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ (Fin D) :=
    { toFun := fun x => ∑ i, (inner ℂ x (b i)) • e (Fin.castLE h i)
      map_add' := by intro x y; simp [inner_add_left, add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul, mul_comm] }
  refine ⟨⟨f, fun x => ?_⟩⟩
  have h1 : inner ℂ (f x) (f x) = ∑ i, (starRingEnd ℂ) (inner ℂ x (b i)) * inner ℂ x (b i) :=
    ho.inner_sum _ _ _
  have h2 := b.sum_inner_mul_inner x x
  have h3 : inner ℂ (f x) (f x) = inner ℂ x x := by
    rw [h1, ← h2]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_conj_symm, mul_comm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖f x‖^2 = ‖x‖^2 := by exact_mod_cast h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem exists_innerProductSpace (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ip : V → V → ℂ)
    (hs : ∀ x y, (starRingEnd ℂ) (ip y x) = ip x y) (hp : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (ha : ∀ x y z, ip (x+y) z = ip x z + ip y z) (hm : ∀ x y (r:ℂ), ip (r • x) y = (starRingEnd ℂ) r * ip x y) :
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : FiniteDimensional ℂ U) (e : U ≃ₗ[ℂ] V),
      ∀ x y, inner ℂ x y = ip (e x) (e y) := by
  let c : InnerProductSpace.Core ℂ V :=
    { inner := ip, conj_inner_symm := hs
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · have := hm x x 0; subst h; simp at this; simp [this]
        · exact (hp x h).le
      add_left := ha, smul_left := hm
      definite := fun x h => by by_contra h'; have := hp x h'; rw [h] at this; simp at this }
  letI n : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI i : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  exact ⟨V, n, i, inferInstance, LinearEquiv.refl _ _, fun x y => rfl⟩

theorem exists_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) :
    ∃ S : SStage B C W, S.s.Del = Del ∧ S.s.letter = letter ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∀ u u', Nonempty (S.s.Pair u u') := by
  have hloc := by
    letI := B.host.cmStar
    exact exists_locAt_split_iff B B.sp.cm.deg2 (conjF_ne_id B)
  choose L hL using hloc
  let pt : Formalism.MainNotions.S.Point B.host.E (B.R.rS + 1) := ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
  have hU := fun u => by
    haveI := (C.mem u).A.Mu0_fd
    exact exists_innerProductSpace (C.mem u).A.Mu0 (fun x y => (C.fm u).ipC 0 x.1 y.1) (fun x y => hs u _ x.2 _ y.2)
      (fun x hx => hp u _ x.2 (fun h => hx (Subtype.ext h)))
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun x y r => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  choose U n i f e he using hU
  obtain ⟨sE⟩ := nonempty_conj_embedding W.EE _ _ hDD W.onb
  let s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW :=
    { cdScale := fun _ _ => 1, cdScale_pos := fun _ _ => one_pos, Del := Del, Del_pos := hD, cloud_gap := gap
      letter := letter, letter_inj := hinj, u_letter := hu, HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := U, cuN := n, cuI := i, cuF := f, Pu := fun _ => 0, volN := fun _ => 1, volH := fun _ => 1
      volN_pos := fun _ => one_pos, volH_pos := fun _ => one_pos, Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0, isId := fun _ => True, inS := fun _ => True, relevant := fun _ => True
      FeqF := fun _ => True, Gterm := fun _ => 0, atP := L, PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False, generic := fun _ => False, Pair := fun _ _ => Unit
      pfst := fun _ => (), psnd := fun _ => (), s0 := fun _ => 0, scalarPair := fun _ => True
      pval := fun _ => 0, ptOf := fun _ => pt, cTerm := fun _ => 1, massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
  exact ⟨{ dsig := fun _ => 1, dsig_pos := fun _ => one_pos, s := s, s_split := hL, s_HH := by simp [s]
           s_Cu := e, s_PlF := Equiv.refl _, s_Cu_isom := he, sEE := sE },
    rfl, rfl, fun _ _ => ⟨()⟩, fun _ _ => ⟨()⟩⟩

theorem nonempty_sStage (B : Base) (C : Cols B) (W : RowsRest B C)
    (Del : ℚ) (hD : 0 < Del)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (letter : B.Word → Fin (B.R.k - 2) → Bool) (hinj : Function.Injective letter)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (hs : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0, (starRingEnd ℂ) ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y)
    (hp : ∀ u, ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re)
    (hDD : W.Drows ≤ W.Dall) : Nonempty (SStage B C W) :=
  (exists_sStage B C W Del hD gap letter hinj hu hs hp hDD).elim fun S _ => ⟨S⟩

end GlobalTheory.Mem.SStageInhab

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem coeFn_sum_smul {α : Type} [MeasurableSpace α] {μ : Measure α} {ι : Type} [Fintype ι] (c : ι → ℂ)
    (u : ι → Lp ℂ 2 μ) :
    ((∑ i, c i • u i : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] fun x => ∑ i, c i * (u i : α → ℂ) x := by
  first
  | exact @_root_.GlobalTheory.FinsetSumSmulCoe.main
  | exact _root_.GlobalTheory.FinsetSumSmulCoe.main
  | (apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinsetSumSmulCoe.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinsetSumSmulCoe.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinsetSumSmulCoe.main ..)

theorem sum_smul_apply {ι α : Type} [Fintype ι] (L : ι → (α → ℂ) →ₗ[ℂ] (α → ℂ)) (c : ι → ℂ) (φ : α → ℂ) (y : α) :
    (∑ i, c i • L i) φ y = ∑ i, c i * L i φ y := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  simp

theorem iotaX_symm_rat {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : X.B.I.GA)
    (hz : z ∈ X.B.I.GFset) : (iotaX X h).symm z ∈ GQ (D.sp.Y 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (z : I.GA), z ∈ I.GFset →
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm z ∈ GQ (D.sp.Y 0) := by
    intro I hI z hz
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm z =
        (Formalism.IndefR.RationalEmbedding.iota D).symm z := rfl
    rw [e, Formalism.IndefR.RationalEmbedding.iota_rat, ContinuousMulEquiv.apply_symm_apply]
    exact hz
  exact aux X.B.I h z hz

theorem ev_translate {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G')
    (red : X.B.I.Gf → G0g D.nd) (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F)
    (k : X.B.I.Gf) (hk : k ∈ X.B.I.Kset) (x : X.B.I.GA) :
    ev (MP R) v₀ S ((iotaX X h).symm (x * (1, k)) * t) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
  have hk' := hB.2 k hk S hS v₀ ((iotaX X h).symm x * t)
  refine Eq.trans ?_ hk'
  have e : (iotaX X h).symm (x * (1, k)) * t = (iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k) := by
    unfold kap
    rw [map_mul]
    group
  show S v₀ _ = S v₀ _
  rw [e]
  rfl

theorem evalAct_intertwines : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) [Fintype (G0g D.nd)] (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd), LevelMatchB R F X h t σ red → ∀ S ∈ MultR R F, ∀ f : L2X X, (f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → (∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g) → ∀ (a : G0g D.nd → ℂ) (s : G0g D.nd → X.B.I.Gf), (∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ) → (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) =ᵐ[muX X] fun x => gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (fun g => star (a (σ.symm g))) (S v₀) ((iotaX X h).symm x * t) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F _ X h t v₀ σ red hB S hS f hf hinv a s hs
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec

  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      ev (MP R) v₀ S ((iotaX X h).symm (γ * y) * t) = ev (MP R) v₀ S ((iotaX X h).symm y * t) := by
    intro γ hγ y
    show S v₀ _ = S v₀ _
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have key : ∀ k ∈ X.B.I.Kset, ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red k))) (S v₀) ((iotaX X h).symm x * t) := by
    intro k hk
    have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
      Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
    have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
      have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
      rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
    obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
    have e1 := X.B.R_spec (1, k) f
    have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
        ev (MP R) v₀ S ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
      refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = ev (MP R) v₀ S ((iotaX X h).symm y * t)) h1 ?_
      rw [h2]
      exact hf
    filter_upwards [e1, e3] with x a1 a3
    rw [a1]
    show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
    rw [a3]
    obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
    rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
      hφinv γ hγ]
    exact ev_translate R F X h t v₀ σ red hB S hS k hk x
  have hall : ∀ᵐ x ∂(muX X), ∀ γ, ((X.B.R (1, s γ) f : L2X X) : X.B.I.GA → ℂ) x =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (σ (red (s γ)))) (S v₀) ((iotaX X h).symm x * t) :=
    ae_all_iff.2 fun γ => key (s γ) (hs γ).1
  have hsum := coeFn_sum_smul (μ := muX X) (fun γ => star (a γ)) (fun γ => star (X.B.R (1, s γ) (star f)))
  filter_upwards [hsum, hall] with x b1 b2
  rw [b1]
  simp only [Formalism.L2.SG.Pf.RowDictPf.R_star, star_star]
  simp only [b2, (hs _).2]
  unfold gaL
  refine Eq.trans ?_ (sum_smul_apply _ _ _ _).symm
  refine Fintype.sum_equiv σ.toEquiv _ _ (fun γ => ?_)
  show _ = star (a (σ.symm (σ γ))) * _
  rw [MulEquiv.symm_apply_apply]
  rfl

end GlobalTheory.Mem.SRe

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) := by
  first | exact @GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one | exact GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one | (intros; apply GlobalTheory.FrameOffPlace.cpt_conj_finE_eq_one <;> assumption)
end
