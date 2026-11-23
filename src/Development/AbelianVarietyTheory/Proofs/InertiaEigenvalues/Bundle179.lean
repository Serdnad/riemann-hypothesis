module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle157
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle004
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues.FrobPow

open Polynomial

theorem eq_of_pow_eq_self_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k]
    (φ : O →+* k) (q : ℕ) (hq : (q : k) = 0) {y z : O} (hy : y ^ q = y) (hz : z ^ q = z)
    (h : φ y = φ z) : y = z := by
  have h1 := Commute.geom_sum₂_mul (Commute.all y z) q
  rw [hy, hz] at h1
  have h2 : ((∑ i ∈ Finset.range q, y ^ i * z ^ (q - 1 - i)) - 1) * (y - z) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exfalso
    have h4 := congrArg φ h3

    simp only [map_sub, map_sum, map_mul, map_pow, map_one, map_zero, h] at h4
    rw [geom_sum₂_self, hq, zero_mul, zero_sub, neg_eq_zero] at h4
    exact one_ne_zero h4
  · exact sub_eq_zero.1 h3

theorem exists_forall_eq_pow_of_pow_eq_self (l : ℕ) [Fact l.Prime] {O k : Type} [CommRing O]
    [IsDomain O] [Field k] [CharP k l] (φ : O →+* k) (τ : O →+* O)
    (hτ : ∀ x, φ x = 0 → φ (τ x) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ, ∀ x : O, x ^ l ^ n = x → τ x = x ^ l ^ a := by
  classical
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let S : Set O := {x | x ^ l ^ n = x}
  have hmon : ∀ (A : Type) [CommRing A] [Nontrivial A], (X ^ l ^ n - X : A[X]).Monic := by
    intro A _ _
    apply Monic.sub_of_left (monic_X_pow _)
    rw [degree_X, degree_X_pow]
    exact_mod_cast hq
  have hS : S.Finite := by
    refine (X ^ l ^ n - X : O[X]).roots.toFinset.finite_toSet.subset fun x hx => ?_
    have hx' : x ^ l ^ n = x := hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [mem_roots (hmon O).ne_zero]
    simp [hx']
  have hint : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    have hx' : x ^ l ^ n = x := hx
    exact ⟨X ^ l ^ n - X, hmon ℤ, by simp [hx']⟩
  have hfin : Module.Finite ℤ (Algebra.adjoin ℤ S) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hS hint
  let ι : Algebra.adjoin ℤ S →+* O := (Algebra.adjoin ℤ S).val.toRingHom
  obtain ⟨a, ha⟩ := GlobalTheory.exists_forall_eq_pow_of_ker_le l (Algebra.adjoin ℤ S) k (φ.comp ι)
    (φ.comp (τ.comp ι)) (fun x hx => hτ _ hx)
  refine ⟨a, fun x hx => ?_⟩
  have h1 : φ (τ x) = φ x ^ l ^ a := ha ⟨x, Algebra.subset_adjoin hx⟩
  refine eq_of_pow_eq_self_of_map_eq φ (l ^ n) ?_ ?_ ?_ ?_
  · rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.ne']
  · rw [← map_pow, hx]
  · rw [← pow_mul, mul_comm, pow_mul, hx]
  · rw [h1, map_pow]

theorem exists_gal_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) (σ : GQ l) :
    ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a := by
  have hl : l.Prime := Fact.out
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.one_lt
  let v : Valuation (Om l) NNReal := (PadicAlgCl.valued l).v
  have hv : ∀ x : Om l, v (σ x) = v x := fun x =>
    NNReal.eq (spectralNorm_eq_of_equiv σ x).symm
  let O : ValuationSubring (Om l) := v.valuationSubring
  have hO : ∀ x : Om l, x ∈ O ↔ v x ≤ 1 := fun x => Iff.rfl
  have hm : ∀ x : O, IsLocalRing.residue O x = 0 ↔ v x < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff _ v
  have hch : CharP (IsLocalRing.ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl).2 ?_
    rw [← map_natCast (IsLocalRing.residue O), hm]
    have : v (l : Om l) = 1 / (l : NNReal) := PadicAlgCl.valuation_p l
    rw [SubringClass.coe_natCast, this, one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  let τ : O →+* O := (σ : Om l →+* Om l).restrict O O (fun x hx => by
    rw [hO] at hx ⊢
    exact (hv x).trans_le hx)
  have hτ : ∀ x : O, ((τ x : O) : Om l) = σ x := fun x => rfl
  obtain ⟨a, ha⟩ := exists_forall_eq_pow_of_pow_eq_self l (IsLocalRing.residue O) τ
    (fun x hx => by rw [hm] at hx ⊢; rw [hτ, hv]; exact hx) n hn
  refine ⟨a, fun x hx => ?_⟩
  have hxO : x ∈ O := by
    rw [hO]
    by_contra h
    have h' : 1 < v x := not_le.1 h
    have h2 : v x ^ 1 < v x ^ l ^ n := pow_lt_pow_right₀ h' hq
    rw [← map_pow, ← map_pow, hx, pow_one] at h2
    exact lt_irrefl _ h2
  have h3 := ha ⟨x, hxO⟩ (Subtype.ext (by simpa using hx))
  have h4 := congrArg (fun y : O => (y : Om l)) h3
  simpa [hτ] using h4

end GlobalTheory.InertiaEigenvalues.FrobPow
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BaseCoef

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

abbrev incl {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥LL.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
  IntermediateField.inclusion h

def IsLatBasis {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : Prop :=
  (∀ i, b i ∈ T.L.T) ∧ ∀ x ∈ T.L.T, ∀ i, b.repr x i ∈ OL LL

def matRep {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL.1 :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp T.ρ

def matRepExt {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL'.1 :=
  ((incl h).mapMatrix : Matrix (Fin k) (Fin k) ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin k) (Fin k) ↥LL'.1).toRingHom.toMonoidHom.comp
    (matRep T b)

def intVec (LL' : FinExt l) (k : ℕ) : Submodule ↥(OL LL') (Fin k → ↥LL'.1) where
  carrier := {v | ∀ i, v i ∈ OL LL'}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c v hv i => by
    rw [Pi.smul_apply, Subalgebra.smul_def]
    exact mul_mem c.2 (hv i)

theorem incl_integral {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {x : ↥LL.1} (hx : x ∈ OL LL) :
    incl h x ∈ OL LL' := by
  have hx' : IsIntegral ℤ_[l] x := hx
  exact hx'.map ((incl h).restrictScalars ℤ_[l])

theorem rep_apply {F : Type} [Field F] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) F) (g : G) (x : Fin k → F) :
    CJ.rep M g x = (M g).mulVec x := rfl

set_option synthInstance.maxHeartbeats 400000

def intVecEquiv (LL' : FinExt l) (k : ℕ) : ↥(intVec LL' k) ≃ₗ[↥(OL LL')] (Fin k → ↥(OL LL')) where
  toFun v := fun i => ⟨(v : Fin k → ↥LL'.1) i, v.2 i⟩
  invFun w := ⟨fun i => (w i : ↥LL'.1), fun i => (w i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_integral {LL : FinExt l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ}
    {b : Module.Basis (Fin k) ↥LL.1 T.V} (hb : IsLatBasis T b) (g : G) (i j : Fin k) :
    matRep T b g i j ∈ OL LL := by
  rw [matRep, MonoidHom.comp_apply]
  change LinearMap.toMatrix b b (T.ρ g) i j ∈ OL LL
  rw [LinearMap.toMatrix_apply]
  exact hb.2 _ (T.L.stable g _ (hb.1 j)) i

abbrev extLat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) : LocLat G ℚ_[l] ↥LL'.1 ↥(OL LL') where
  V := Fin k → ↥LL'.1
  ρ := CJ.rep (matRepExt h T b)
  cont x := by
    refine continuous_pi fun i => ?_
    simp only [rep_apply, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
    have h1 : Continuous fun g => b.coord i (T.ρ g (b j)) :=
      (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (T.cont (b j))
    have h2 : Continuous (incl h) := continuous_subtype_val.subtype_mk _
    refine (h2.comp h1).congr fun g => ?_
    simp [matRepExt, matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  L :=
    { T := intVec LL' k
      stable := fun g x hx i => by
        simp only [rep_apply, Matrix.mulVec, dotProduct]
        refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hx j)
        exact incl_integral h (repr_integral hb g i j)
      fg := by
        haveI : Module.Finite ↥(OL LL') ↥(intVec LL' k) := Module.Finite.equiv (intVecEquiv LL' k).symm
        exact Module.Finite.iff_fg.1 inferInstance
      free := Module.Free.of_equiv (intVecEquiv LL' k).symm
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL'.1 (Fin k)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩ j
        rw [Pi.basisFun_apply]
        by_cases hij : i = j
        · subst hij; simp [one_mem]
        · simp [Pi.single_apply, Ne.symm hij, zero_mem] }

theorem hom_integral {LL : FinExt l} {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (i : Fin k₂) (j : Fin k₁) :
    LinearMap.toMatrix b₁ b₂ F.f i j ∈ OL LL := by
  rw [LinearMap.toMatrix_apply]
  exact hb₂.2 _ (F.T_le _ (hb₁.1 j)) i

def extMat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L) :
    Matrix (Fin k₂) (Fin k₁) ↥LL'.1 :=
  (LinearMap.toMatrix b₁ b₂ F.f).map (incl h)


theorem extMat_comm {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L)
    (g : G) : extMat h b₁ b₂ F * matRepExt h T₁ b₁ g = matRepExt h T₂ b₂ g * extMat h b₁ b₂ F := by
  have e1 : matRepExt h T₁ b₁ g = (LinearMap.toMatrix b₁ b₁ (T₁.ρ g)).map (incl h) := rfl
  have e2 : matRepExt h T₂ b₂ g = (LinearMap.toMatrix b₂ b₂ (T₂.ρ g)).map (incl h) := rfl
  have key : LinearMap.toMatrix b₁ b₂ F.f * LinearMap.toMatrix b₁ b₁ (T₁.ρ g) =
      LinearMap.toMatrix b₂ b₂ (T₂.ρ g) * LinearMap.toMatrix b₁ b₂ F.f := by
    have c1 := LinearMap.toMatrix_comp b₁ b₁ b₂ F.f (T₁.ρ g)
    have c2 := LinearMap.toMatrix_comp b₁ b₂ b₂ (T₂.ρ g) F.f
    have hc : F.f ∘ₗ T₁.ρ g = T₂.ρ g ∘ₗ F.f := LinearMap.ext fun y => F.equiv g y
    rw [← c1, ← c2, hc]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M => incl h (M i j)) key

  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simpa only [e1, e2, Matrix.mul_apply, extMat, Matrix.map_apply] using this

def extHom {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) :
    LatHom (extLat h T₁ b₁ hb₁).L (extLat h T₂ b₂ hb₂).L where
  f := Matrix.toLin' (extMat h b₁ b₂ F)
  equiv g x := by
    change (extMat h b₁ b₂ F).mulVec ((matRepExt h T₁ b₁ g).mulVec x) =
      (matRepExt h T₂ b₂ g).mulVec ((extMat h b₁ b₂ F).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, extMat_comm]
  cont := LinearMap.continuous_on_pi _
  T_le x hx i := by
    change (extMat h b₁ b₂ F).mulVec x i ∈ OL LL'
    simp only [Matrix.mulVec, dotProduct, extMat, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (incl_integral h (hom_integral hb₁ hb₂ F i j)) (hx j)

def mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL') (Sig : Finset (I →* LLˣ)) :
    Finset (I →* LL'ˣ) := by
  classical
  exact Sig.image fun a => (Units.map (f : LL →* LL')).comp a

end GlobalTheory.BaseCoef
end
end

section

noncomputable section

namespace GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  have h : Function.Injective
      (LinearMap.lTensor V (PD.ι.toLinearMap.restrictScalars Qp)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ PD.ι_inj
  exact h

theorem ιV_actVB (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp [ιV, actVB, actVdR, PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_Dcris_le (ρ : Representation LL G V) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) ≤ DdR PD ρ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  simp only [Dcris, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero] at hx ⊢
  intro g
  rw [← ιV_actVB, hx g]

theorem DdR_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(DdR PD ρ) := by
  by_cases hV : finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    have h0 : ∀ x : V ⊗[Qp] BdR, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
      | add a c ha hc => rw [ha, hc, add_zero]
    haveI : Subsingleton ↥(DdR PD ρ) :=
      ⟨fun x y => Subtype.ext ((h0 x).trans (h0 y).symm)⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem Dcris_finite [FiniteDimensional Qp K] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (h : IsDR PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := DdR_finite PD ρ h
  haveI : FiniteDimensional LL ↥((Dcris PD ρ).map (ιV PD (LL := LL) (V := V))) :=
    Submodule.finiteDimensional_of_le (map_Dcris_le PD ρ)
  exact Module.Finite.equiv
    (Submodule.equivMapOfInjective _ (ιV_injective PD) (Dcris PD ρ)).symm

end Generic

end GlobalTheory.DcrisFin

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

theorem GlobalTheory.DcrisFin.dcris_finite_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsDR (P.PD K) ρ → Module.Finite ℚ_[l] ↥(Dcris (P.PD K) ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI := (P.PD K).finK
  exact GlobalTheory.DcrisFin.Dcris_finite (P.PD K) ρ h
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  first | exact @GlobalTheory.cobO_iff_forall_lam | exact GlobalTheory.cobO_iff_forall_lam | (intros; apply GlobalTheory.cobO_iff_forall_lam <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.cup_one_cocycles_anticomm_up_to_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  first | exact @GlobalTheory.cupL_anticomm_cobL | exact GlobalTheory.cupL_anticomm_cobL | (intros; apply GlobalTheory.cupL_anticomm_cobL <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  first | exact @GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | exact GlobalTheory.BKTorsionRed.mem_HfQ_iff_red | (intros; apply GlobalTheory.BKTorsionRed.mem_HfQ_iff_red <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.dualLattice_stable_twisted_pairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.DualLat.dualLattice_exists | exact GlobalTheory.DualLat.dualLattice_exists | (intros; apply GlobalTheory.DualLat.dualLattice_exists <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.span_cyclotomic_twoCocycles_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∃ z0 : ↥(GK K) × ↥(GK K) → ℚ_[l], (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → ℚ_[l], Continuous z → (∀ g h k, ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : ℚ_[l], CobL (P.PD K) (z - x • z0)) → ∃ z0 : ↥(GK K) × ↥(GK K) → LL, (Continuous z0 ∧ ∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z0 (h, k) - z0 (g * h, k) + z0 (g, h * k) - z0 (g, h) = 0) ∧ ∀ z : ↥(GK K) × ↥(GK K) → LL, Continuous z → (∀ g h k, ((cycLL (P.PD K) LL g : LLˣ) : LL) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ x : LL, CobL (P.PD K) (z - x • z0) := by
  first | exact @GlobalTheory.span_cocycles_cyc_ext | exact GlobalTheory.span_cocycles_cyc_ext | (intros; apply GlobalTheory.span_cocycles_cyc_ext <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.torsionCocycle_uniformizer_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', ∃ r : ℕ, ∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T := by
  first | exact @GlobalTheory.TorsCoc.cocycle_pow_smul_mem | exact GlobalTheory.TorsCoc.cocycle_pow_smul_mem | (intros; apply GlobalTheory.TorsCoc.cocycle_pow_smul_mem <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.IrrQuot

theorem main : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (s : Finset V), Nontrivial V → Submodule.span ℂ {w | ∃ g : G, ∃ v ∈ s, w = ρ g v} = ⊤ → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), τ.IsIrreducible ∧ ∃ f : ρ.IntertwiningMap τ, Function.Surjective f := by
  intro G V _ _ _ ρ s hV hspan
  have key : ∀ T : Subrepresentation ρ, (∀ v ∈ s, v ∈ T.toSubmodule) → T = ⊤ := by
    intro T hT
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro w ⟨g, v, hv, rfl⟩
    exact T.apply_mem_toSubmodule g (hT v hv)
  haveI : Module.Finite (MonoidAlgebra ℂ G) ρ.asModule := by
    let t : Finset ρ.asModule := s
    refine ⟨⟨t, ?_⟩⟩
    have h := key (Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)))
      (fun v hv => Submodule.subset_span (R := MonoidAlgebra ℂ G) (s := (t : Set ρ.asModule)) hv)
    refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ Subrepresentation.ofSubmodule' (Submodule.span (MonoidAlgebra ℂ G) (t : Set ρ.asModule)) := by
      rw [h]; trivial
    exact hx
  haveI : IsCoatomic (Subrepresentation ρ) :=
    (OrderIso.isCoatomic_iff Subrepresentation.subrepresentationSubmoduleOrderIso).2 inferInstance
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at this
    exact hv this
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  refine ⟨_, inferInstance, inferInstance, GlobalTheory.SmGL.subQuot ⊤ M, GlobalTheory.SmGL.isIrreducible_subQuot hM.covBy_top, ?_⟩
  refine ⟨⟨(Submodule.mkQ _).comp (LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial)), fun g => rfl⟩, ?_⟩
  intro y
  obtain ⟨⟨v, _⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end GlobalTheory.IrrQuot
end
