module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle043
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle027
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.sqrtNegPrime_kernel_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  first | exact @GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | exact GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | (intros; apply GlobalTheory.CMModel.ker_sqrtNegNat_cyclic <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

namespace GlobalTheory.LieVB

theorem bijective_add_mul_epsFn : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  intro O _ V hV
  have H : IsPullback (spMap (algebraMap O (DualNumber O))) (𝟙 _) (𝟙 _)
      (spMap (algebraMap O (DualNumber O))) := IsPullback.of_vert_isIso ⟨by simp⟩
  have h := GlobalTheory.EpsThick.comb_bijective_of_isAffineOpen H hV
  refine Eq.mpr (congrArg Function.Bijective (funext fun ab => ?_)) h
  rw [Scheme.Hom.appLE_eq_app, _root_.mul_comm]
  rfl

end GlobalTheory.LieVB
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

section Defs

variable {O : Type} [CommRing O]

def IsActPull {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] (i' : OAct O G') (i : OAct O G)
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  IsGrpPullback G' G f φ ∧ ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left

def IsCover (k : Type) [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [Algebra k Γ(C', ⊤)] (π : C' ⟶ C) : Prop :=
  IsFinite π ∧ Surjective π ∧ π ≫ strHom k C = strHom k C'

def IsRosati (c : O →+* O) {S : Scheme.{0}} (P : Out.PolAV S) (j : OAct O P.A) : Prop :=
  ∀ a, Out.RosatiAdj P.A P.L (j.act a) (j.act (c a))

def PolPart (c : O →+* O) {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (T : TorusExtension G) (P : Out.PolAV (Sp K)) (e : T.B ≅ P.A) (j : OAct O P.A),
    IsMonHom (T.q ≫ e.hom) ∧ (∀ a, i.act a ≫ T.q ≫ e.hom = (T.q ≫ e.hom) ≫ j.act a) ∧ IsRosati c P j

def genPt (C : Scheme.{0}) [IsIntegral C] : Sp C.functionField ⟶ C := C.fromSpecStalk (genericPoint C)

def geomGenPt (C : Scheme.{0}) [IsIntegral C] : Sp (AlgebraicClosure C.functionField) ⟶ C :=
  spMap (algebraMap C.functionField (AlgebraicClosure C.functionField)) ≫ genPt C

def PolGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (G' : Over (Sp (AlgebraicClosure C.functionField))) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left),
    IsActPull i' i (geomGenPt C) φ ∧ PolPart c i'

def AbGen (c : O →+* O) {C : Scheme.{0}} [IsIntegral C] {G : Over C} [GrpObj G] (i : OAct O G) : Prop :=
  ∃ (P : Out.PolAV (Sp C.functionField)) (j : OAct O P.A) (φ : P.A.left ⟶ G.left),
    IsActPull j i (genPt C) φ ∧ IsRosati c P j

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
  {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Defs

def Splits (O k : Type) [CommRing O] [Field k] : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (τ : κ → (O →+* k)), IsSplitBy τ

section Lemmas

variable {O : Type} [CommRing O]

theorem IsActPull.comp {S S' S'' : Scheme.{0}} {G'' : Over S''} [GrpObj G''] {G' : Over S'} [GrpObj G'] {G : Over S}
    [GrpObj G] {i'' : OAct O G''} {i' : OAct O G'} {i : OAct O G} {g : S'' ⟶ S'} {f : S' ⟶ S} {φ' : G''.left ⟶ G'.left}
    {φ : G'.left ⟶ G.left} (h' : IsActPull i'' i' g φ') (h : IsActPull i' i f φ) : IsActPull i'' i (g ≫ f) (φ' ≫ φ) :=
  ⟨h'.1.comp h.1, fun a => by rw [← Category.assoc, h'.2, Category.assoc, h.2, Category.assoc]⟩

end Lemmas

end GlobalTheory.CurveRootGeometry
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.NefRR

theorem abs_chi_sub_hdim_zero_add_hdim_one_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (n : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (n : ℕ) → ∀ e : ℕ → ℕ, (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * e m)) → ∃ C : ℕ, ∀ m : ℕ, |chi k (twist F (lbPow L m)) - (hdim k (twist F (lbPow L m)) 0 : ℤ) + (hdim k (twist F (lbPow L m)) 1 : ℤ)| ≤ C * (e m : ℤ) := by
  intro k _ _ X _ hp n L hL F _ hF e he
  choose C hC using fun i : ℕ => he (i + 2) (by omega)
  refine ⟨∑ i ∈ Finset.range n, C i, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  haveI : IsFiniteQC (twist F (lbPow L m)) := isFiniteQC_twist hM
  have hv : ∀ i, n + 2 ≤ i → Subsingleton (coh (twist F (lbPow L m)) i) := fun i hi =>
    subsingleton_coh_of_isProjOver hp _
      (((suppDim_twist hM).trans_le hF).trans_lt (by exact_mod_cast (by omega : n < i)))
  rw [chi_eq_sum_range k (n + 2) hv, Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ a b c : ℤ, a + (-1 : ℤ) ^ (0 + 1) * b + (-1 : ℤ) ^ 0 * c - c + b = a := by
    intro a b c; ring
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  exact_mod_cast hC i m

end GlobalTheory.NefRR
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le_zero : ∀ (k : Type) [Field k] [Infinite k], (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (0 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ Y _ hp hd A N hA hN
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hp
  have hAN : (tens A N).IsLB := (IsNef.tens_of_isProjOver (IsAmpleLB.isNef (k := k) hA) hN hp).isLB
  have hlt : topologicalKrullDim Y < ((1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.zero_lt_one)
  refine isAmpleLB_of_subsingleton_coh_one Y (tens A N) hAN fun F _ => ⟨1, le_rfl, ?_⟩
  have : IsFiniteQC (twist F (lbPow (tens A N) 1)) := isFiniteQC_twist (isLB_lbPow hAN 1)
  exact hA.subsingleton_coh_of_dim_lt _ hlt

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_nonneg_of_isAmpleLB_of_isProjOver :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)],
      IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) →
        ∀ P : Fin d → LB X, (∀ i, IsAmpleLB (P i)) → 0 ≤ interNum k F P := by
  intro k _ _ X _ hp d
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hd P _
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd]
    exact Nat.cast_nonneg _
  | succ d ih =>
    intro F _ hd P hP
    obtain ⟨n, hn, s, hs, -⟩ := (hP 0).exists_mono_cutHom F
    have hL := isLB_lbPow (hP 0).isLB n
    have h1 := ih (cut F hL s) (suppDim_cut_le F hL s hd) (Fin.tail P) fun i => hP i.succ
    rw [← interNum_cons_eq_interNum_cut hL s (P := Fin.tail P) (fun i => (hP i.succ).isLB)
      (finiteCohTwists_of_isProjOver hf F hp)] at h1
    have h2 := (diffVanish_chiPic_of_isProjOver hf F hp hd).interNum_update_of_cls_eq_zsmul
      (L := P) (by simp) (fun i => (hP i).isLB) 0 hL (hP 0).isLB (n : ℤ)
      (by rw [cls_lbPow (hP 0).isLB, natCast_zsmul])
    have e : Function.update P 0 (lbPow (P 0) n) =
        (Fin.cons (lbPow (P 0) n) (Fin.tail P) : Fin (d + 1) → LB X) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Fin.tail]
    rw [Function.update_eq_self, e] at h2
    rw [h2] at h1
    exact nonneg_of_mul_nonneg_right h1 (Nat.cast_pos.2 hn)

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_cons_ample_nef_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  intro k _ _ X _ hp d hd H A hA P hP
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  have hv := diffVanish_chiPic_of_isProjOver hf (GlobalTheory.structureModule X) hp hsd
  obtain ⟨a, ha, s, hs, -⟩ := hA.exists_mono_cutHom (GlobalTheory.structureModule X)
  have hLa := isLB_lbPow hA.isLB a
  have h0 := H _ (suppDim_cut_le _ hLa s hsd) P hP
  rw [← interNum_cons_eq_interNum_cut hLa s hPb hfin] at h0
  have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons hA.isLB hPb) (0 : Fin (d + 1))
    hLa hA.isLB (a : ℤ) (cls_lbZPow hA.isLB a _)
  simp only [Fin.update_cons_zero] at h
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  intro k _ _ X _ hX L hL S hS h1 h3 i e hb1 hb3
  obtain ⟨C₁, hC₁⟩ := hb1
  obtain ⟨C₃, hC₃⟩ := hb3
  obtain ⟨hP, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k X)).1 hX
  have hf := algebraMap_eq_strHom k X
  have F₁ : FiniteCohTwists k S.X₁ := IsAmpleLB.finiteCohTwists hf S.X₁ hA
  have F₃ : FiniteCohTwists k S.X₃ := IsAmpleLB.finiteCohTwists hf S.X₃ hA
  refine ⟨C₁ + C₃, fun m => ?_⟩
  have hLm : (lbPow L m).IsLB := isLB_lbPow hL m
  have hT := Twist.shortExact_map hLm hS
  have fin₁ := ((F₁.twist hLm).finiteCoh).finite i
  have fin₃ := ((F₃.twist hLm).finiteCoh).finite i
  have key := hdim₂_le k hT i fin₁ fin₃
  calc hdim k (twist S.X₂ (lbPow L m)) i ≤ hdim k (twist S.X₁ (lbPow L m)) i + hdim k (twist S.X₃ (lbPow L m)) i := key
    _ ≤ C₁ * e m + C₃ * e m := Nat.add_le_add (hC₁ m) (hC₃ m)
    _ = (C₁ + C₃) * e m := (Nat.add_mul C₁ C₃ (e m)).symm

end GlobalTheory
end

section

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_chi_twist_lbPow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hproj d F _ hsupp L hL
  have hv : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hproj hsupp
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := hv.exists_polynomial_int ℚ (cls L hL) 0
  obtain ⟨C, hC⟩ := abs_factorial_mul_eval_sub_top_le d p hpdeg
  refine ⟨C, fun m => ?_⟩
  have hmd : multiDiff (fun _ : Fin d => cls L hL) (chiPic k F) 0 =
      interNum k F (fun _ : Fin d => L) :=
    hv.multiDiff_chiPic (L := fun _ : Fin d => L) (by simp) (fun _ => hL) 0
  have hchi : chi k (twist F (lbPow L m)) = chiPic k F ((m : ℤ) • cls L hL) := by
    rw [← twistZ_natCast]
    exact chi_twistZ k F hL (m : ℤ)
  have heval : p.eval (m : ℚ) = (chi k (twist F (lbPow L m)) : ℚ) := by
    have e := hpeval (m : ℤ)
    rw [zero_add, ← hchi, Int.cast_natCast] at e
    exact e
  have hfac : (d.factorial : ℚ) * p.coeff d = (interNum k F (fun _ : Fin d => L) : ℚ) := by
    rw [hpcoeff, hmd, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]
  have h := hC m
  rw [heval, hfac] at h
  have h' : ((|(d.factorial : ℤ) * chi k (twist F (lbPow L m)) -
      interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      ((C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast h'

end GlobalTheory
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.eventually_isGenerated_tens_lbPow {X : Scheme.{0}} {A N : LB X} (hA : IsAmpleLB A)
    (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsGenerated (tens N (lbPow A n)) := by
  have := isFiniteQC_twist (F := GlobalTheory.structureModule X) hN
  refine (hA.eventually_isGloballyGenerated_twist (twist (GlobalTheory.structureModule X) N)).mono
    fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hT := isLB_tens hN hP
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule X) hN hP hT
    (cls_tens hN hP hT)
  exact (isGloballyGenerated_toMod_iff hT).1 ((hn.of_epi e.hom).of_epi (unitTwistIso _).hom)

theorem IsAmpleLB.eventually_isAmpleLB_tens_lbPow_succ {X : Scheme.{0}} {A N : LB X}
    (hA : IsAmpleLB A) (hN : N.IsLB) : ∀ᶠ n : ℕ in atTop, IsAmpleLB (tens N (lbPow A (n + 1))) := by
  refine (hA.eventually_isGenerated_tens_lbPow hN).mono fun n hn => ?_
  have hP := isLB_lbPow hA.isLB n
  have hP' := isLB_lbPow hA.isLB (n + 1)
  have hT := isLB_tens hN hP'
  have hD := LB.isLB_div hT hA.isLB
  refine hA.tensor_isGenerated hn hT ((cls_eq_zero_iff (LB.isLB_div hD hn.isLB)).1 ?_)
  rw [cls_div hD hn.isLB, cls_div hT hA.isLB, cls_tens hN hP', cls_tens hN hP,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB, succ_nsmul]
  abel

theorem exists_isAmpleLB_tens_lbPow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ A N : LB X, IsAmpleLB A → N.IsLB → ∃ c : ℕ, 1 ≤ c ∧ IsAmpleLB (tens N (lbPow A c)) := by
  intro k _ _ X _ _ A N hA hN
  obtain ⟨n, hn⟩ := (hA.eventually_isAmpleLB_tens_lbPow_succ hN).exists
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end GlobalTheory
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem isPsEff_pull_redι_univ_of_hasNonzeroSec_pow :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  intro k _ _ X _ _ hp M hM r hr hs Z hZ
  have hirr : IsIrreducible (Z : Set X) := hZ ▸ IrreducibleSpace.isIrreducible_univ X
  have := isIntegral_red hirr
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
  obtain ⟨x, hx⟩ := (range_redι Z).ge (hZ.ge (Set.mem_univ (genericPoint X)))
  rw [← hx] at hs
  have e := nonzeroLocus_secPull s (redι Z)
  have h1 : HasNonzeroSec ((lbPow M r).pull (redι Z)) :=
    ⟨secPull s (redι Z), sec_ne_zero_of_mem (x := x) (e.ge hs)⟩
  have hM' := LB.isLB_pull hM (redι Z)
  refine isPsEff_of_hasNonzeroSec_pow (hH.pull_of_isClosedImmersion (redι Z)) hM' hr
    (h1.of_cls_eq (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _) ?_)
  exact (cls_eq_iff (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _)).2
    (lbIso_lbPow_pull hM (redι Z) r)

end GlobalTheory
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsNef.isPsEff_pull_red_of_dim_le (k : Type) [Field k] [Infinite k] (d : ℕ)
    (H : ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) →
      topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N →
        IsAmpleLB (CechPic.tens A N))
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k (X := X))) (M : LB X)
    (hM : IsNef k M) (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (hd : topologicalKrullDim (Z : Set X) ≤ (d : ℕ)) : IsPsEff (M.pull (redι Z)) := by
  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hZ
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hX
  have : IsProper (strHom k (X := X)) := by
    obtain ⟨N, i, hi, e⟩ := hX
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hA := hB.pull_of_isClosedImmersion (redι Z)
  have : IsProper (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hN := hM.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))
  refine ⟨hN.isLB, _, hA, fun m _ => ?_⟩
  have hP := H _ (hA.isProjOver _) ((topologicalKrullDim_red Z).trans_le hd) _ _ hA (hN.pow hA m)
  obtain ⟨r, hr, hg⟩ := hP.exists_isGenerated_pow
  refine ⟨r, hr, hg.hasNonzeroSec.of_cls_eq
    (isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB) r) hg.isLB ?_⟩
  rw [cls_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB), cls_lbPow hP.isLB,
    cls_tens (isLB_lbPow hN.isLB m) hA.isLB, cls_tens hA.isLB (isLB_lbPow hN.isLB m), add_comm]

end GlobalTheory
end
end
