module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle726
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle061
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle663
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDescentSymmetricLinearisedBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle137
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle734
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle735
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

instance instSupNE (I : Type) : SemilatticeSup {S : Set I // S.Nonempty} :=
  Subtype.semilatticeSup fun _ _ h _ => h.mono Set.subset_union_left

abbrev NE (I : Type) : Type := {S : Set I // S.Nonempty}ᵒᵈ

variable {I : Type} {X : Scheme.{0}}

def NE.set (S : NE I) : Set I := (OrderDual.ofDual S).1

theorem NE.le_iff {S T : NE I} : S ≤ T ↔ T.set ⊆ S.set := Iff.rfl

theorem NE.set_inf (S T : NE I) : (S ⊓ T).set = S.set ∪ T.set := rfl

theorem NE.nonempty (S : NE I) : S.set.Nonempty := (OrderDual.ofDual S).2

def NE.single (i : I) : NE I := OrderDual.toDual ⟨{i}, Set.singleton_nonempty i⟩

def NE.pair (i j : I) : NE I := OrderDual.toDual ⟨{i, j}, Set.insert_nonempty i {j}⟩

theorem NE.set_single (i : I) : (NE.single i).set = {i} := rfl

theorem NE.set_pair (i j : I) : (NE.pair i j).set = {i, j} := rfl

theorem NE.pair_le_single_left (i j : I) : NE.pair i j ≤ NE.single i :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert i {j}))

theorem NE.pair_le_single_right (i j : I) : NE.pair i j ≤ NE.single j :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem i rfl))

def NE.pt (S : NE I) : I := S.nonempty.some

theorem NE.pt_mem (S : NE I) : S.pt ∈ S.set := S.nonempty.some_mem

def cap (U : I → X.Opens) (S : NE I) : X.Opens := ⨅ i ∈ S.set, U i

theorem cap_le (U : I → X.Opens) {S : NE I} {i : I} (h : i ∈ S.set) : cap U S ≤ U i := iInf₂_le i h

theorem cap_mono (U : I → X.Opens) : Monotone (cap U) := fun _ _ h => le_iInf₂ fun i hi => iInf₂_le i (h hi)

theorem cap_inf (U : I → X.Opens) (S T : NE I) : cap U (S ⊓ T) = cap U S ⊓ cap U T := by
  simp only [cap, NE.set_inf, iInf_union]

theorem cap_single (U : I → X.Opens) (i : I) : cap U (NE.single i) = U i := by
  simp [cap, NE.set_single]

theorem cap_pair (U : I → X.Opens) (i j : I) : cap U (NE.pair i j) = U i ⊓ U j := by
  rw [cap, NE.set_pair, iInf_insert, iInf_singleton]

theorem cap_iSup (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ S, cap U S = ⊤ :=
  eq_top_iff.2 (hU ▸ iSup_le fun i => (cap_single U i).symm.le.trans (le_iSup (cap U) (NE.single i)))

theorem isAffineOpen_cap [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) :
    IsAffineOpen (cap U S) := by
  have key : ∀ s : Set I, s.Finite → s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := by
    intro s hs
    obtain ⟨t, rfl⟩ := hs.exists_finset_coe
    classical
    induction t using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a t _ ih =>
      intro _
      rw [Finset.coe_insert]
      rcases (t : Set I).eq_empty_or_nonempty with ht | ht
      · rw [ht, iInf_insert, iInf_emptyset, inf_top_eq]; exact hU a
      · rw [iInf_insert]; exact hinf _ _ (hU a) (ih (Set.toFinite _) ht)
  exact key _ (Set.toFinite _) S.nonempty

def capAff [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) : X.affineOpens :=
  ⟨cap U S, isAffineOpen_cap U hU hinf S⟩

theorem capAff_mono [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) :
    Monotone (capAff U hU hinf) := fun _ _ h => cap_mono U h

section Maps

variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

abbrev capF : (NE I)ᵒᵖ ⥤ CommAlgCat.{0} R := (capAff_mono U hU hinf).functor.op ⋙ OAff s

def cv (T : (NE I)ᵒᵖ) : (capF s U hU hinf).obj T ≃+* Γ(X, cap U T.unop) := RingEquiv.refl _

theorem cv_mp {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T' (mp (capF s U hU hinf) a b) = rsT (cv s U hU hinf T b) (cap U T'.unop) :=
  (GlobalTheory.KS.rsT_of_le (O₀ := cap U T.unop) (cap_mono U (leOfHom a.unop)) b).symm

theorem cv_smul {T : (NE I)ᵒᵖ} (r : R) (b : (capF s U hU hinf).obj T) :
    cv s U hU hinf T (r • b) = constFn s (cap U T.unop) r * cv s U hU hinf T b :=
  Algebra.smul_def r b

def toPos (c : C1 U) : CatCoh.C1 (capF s U hU hinf) :=
  fun T T' _ => (cv s U hU hinf T').symm (rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop))

def toCech (f : CatCoh.C1 (capF s U hU hinf)) : C1 U := fun i j =>
  rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
      (U i ⊓ U j) -
    rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
      (U i ⊓ U j)

theorem cv_toPos (c : C1 U) {T T' : (NE I)ᵒᵖ} (a : T ⟶ T') :
    cv s U hU hinf T' (toPos s U hU hinf c T T' a) = rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop) :=
  RingEquiv.apply_symm_apply _ _

theorem toCech_apply (f : CatCoh.C1 (capF s U hU hinf)) (i j : I) :
    toCech s U hU hinf f i j =
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
        (U i ⊓ U j) -
      rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
        (U i ⊓ U j) := rfl

theorem restrict_capF_bijective (hcov : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (OAff s) (capAff_mono U hU hinf).functor.op).pull1 :=
  GlobalTheory.CoverO.restrict_bijective R X s (NE I) (capAff U hU hinf) (capAff_mono U hU hinf)
    (fun S T => cap_inf U S T) (cap_iSup U hcov)

end Maps

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))

theorem NE.pt_single (i : I) : (NE.single i).pt = i := Set.mem_singleton_iff.1 (NE.pt_mem (NE.single i))

theorem toPos_lc {n : ℕ} (cc : Fin n → R) (b : Fin n → C1 U) :
    toPos s U hU hinf (fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * b a i j) =
      ∑ a, cc a • toPos s U hU hinf (b a) := by
  funext T T' φ
  have hle : cap U T'.unop ≤ U T.unop.pt ⊓ U T'.unop.pt :=
    le_inf (cap_le U ((NE.le_iff.1 (leOfHom φ.unop)) T.unop.pt_mem)) (cap_le U T'.unop.pt_mem)
  apply (cv s U hU hinf T').injective

  simp only [cv_toPos, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
  GlobalTheory.KS.rsT_constFn s hle]

theorem toCech_sub (f f' : CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (f - f') = toCech s U hU hinf f - toCech s U hU hinf f' := by
  funext i j
  simp only [toCech_apply, Pi.sub_apply, map_sub, GlobalTheory.KS.rsT_sub]
  abel

theorem toCech_lc {n : ℕ} (cc : Fin n → R) (f : Fin n → CatCoh.C1 (capF s U hU hinf)) :
    toCech s U hU hinf (∑ a, cc a • f a) =
      fun i j => ∑ a, constFn s (U i ⊓ U j) (cc a) * toCech s U hU hinf (f a) i j := by
  funext i j
  have hle : U i ⊓ U j ≤ cap U (NE.pair i j) := (cap_pair U i j).ge

  simp only [toCech_apply, Finset.sum_apply, Pi.smul_apply, map_sum, cv_smul, GlobalTheory.KS.rsT_sum, GlobalTheory.KS.rsT_mul,
  GlobalTheory.KS.rsT_constFn s hle, mul_sub, Finset.sum_sub_distrib]
  refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => ?_) (Finset.sum_congr rfl fun a _ => ?_) <;>
    rw [cv_smul, GlobalTheory.KS.rsT_mul, GlobalTheory.KS.rsT_constFn s hle]

end GlobalTheory.CechCmp
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

namespace GlobalTheory.CechMixed
open GlobalTheory.KS

theorem coc_on {X : Scheme.{0}} {J : Type} {V : J → X.Opens} {z : C1 V} (hz : IsCoc V z) (i j l : J)
    {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hl : W ≤ V l) :
    rsT (z i j) W + rsT (z j l) W = rsT (z i l) W := by
  have e : W ≤ V i ⊓ V j ⊓ V l := le_inf (le_inf hi hj) hl
  have h := congrArg (fun s => rsT s W) (hz i j l)
  simp only [rsT_add] at h
  rwa [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e] at h

theorem le_iSup_inf {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) (O : X.Opens) :
    O ≤ ⨆ i, V i ⊓ O := by
  rw [← iSup_inf_eq, hV, top_inf_eq]

theorem exists_split {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) {O : X.Opens}
    (hO : IsAffineOpen O) {z : C1 V} (hz : IsCoc V z) :
    ∃ b : ∀ i, Γ(X, V i ⊓ O), ∀ i i' (W : X.Opens), W ≤ V i → W ≤ V i' → W ≤ O →
      rsT (z i i') W = rsT (b i) W - rsT (b i') W := by
  have hs : ⨆ i, V i ⊓ O = O := by rw [← iSup_inf_eq, hV, top_inf_eq]
  have hle : ∀ i j, V i ⊓ O ⊓ (V j ⊓ O) ≤ V i ⊓ V j := fun i j => inf_le_inf inf_le_left inf_le_left
  obtain ⟨y, hy⟩ := isCob_of_isAffineOpen X J (fun i => V i ⊓ O)
    (fun i j => rsT (z i j) (V i ⊓ O ⊓ (V j ⊓ O))) (hs.symm ▸ hO) (by
      intro i j l
      dsimp only
      rw [rsT_rsT (hle i j) inf_le_left,
        rsT_rsT (hle j l) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
        rsT_rsT (hle i l) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
      exact coc_on hz i j l ((inf_le_left.trans inf_le_left).trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left))
  refine ⟨fun i => - y i, fun i i' W h h' hW => ?_⟩
  have e : W ≤ V i ⊓ O ⊓ (V i' ⊓ O) := le_inf (le_inf h hW) (le_inf h' hW)
  have k := congrArg (fun s => rsT s W) (hy i i')
  simp only [rsT_sub] at k
  rw [rsT_rsT (hle i i') e, rsT_rsT inf_le_right e, rsT_rsT inf_le_left e] at k
  simp only [rsT_neg]
  rw [k]; ring

theorem exists_cocycle_on_affine : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  intro X J K V U hV hU z hz
  choose b hb using fun k => exists_split hV (hU k) hz
  have glue : ∀ k k', ∃ t : Γ(X, U k ⊓ U k'), ∀ i, rsT t (V i ⊓ (U k ⊓ U k')) =
      rsT (b k' i) (V i ⊓ (U k ⊓ U k')) - rsT (b k i) (V i ⊓ (U k ⊓ U k')) := by
    intro k k'
    refine exists_rsT_eq (fun i => V i ⊓ (U k ⊓ U k')) (fun i => inf_le_right)
      (le_iSup_inf hV _) _ fun i j => ?_
    simp only [rsT_sub]
    rw [rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_right,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_right]
    have hi : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V i := inf_le_left.trans inf_le_left
    have hj : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V j := inf_le_right.trans inf_le_left
    have hk : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ U k ⊓ U k' := inf_le_right.trans inf_le_right
    have h1 := hb k i j _ hi hj (hk.trans inf_le_left)
    have h2 := hb k' i j _ hi hj (hk.trans inf_le_right)
    linear_combination h1 - h2
  choose t ht using glue
  have ht' : ∀ k k' i (W : X.Opens), W ≤ V i → W ≤ U k → W ≤ U k' →
      rsT (t k k') W = rsT (b k' i) W - rsT (b k i) W := by
    intro k k' i W hi hk hk'
    have e : W ≤ V i ⊓ (U k ⊓ U k') := le_inf hi (le_inf hk hk')
    have h := congrArg (fun s => rsT s W) (ht k k' i)
    simp only [rsT_sub] at h
    rwa [rsT_rsT inf_le_right e, rsT_rsT (inf_le_inf_left _ inf_le_right) e,
      rsT_rsT (inf_le_inf_left _ inf_le_left) e] at h
  refine ⟨t, fun i k => b k i, fun k k' k'' => ?_, fun i i' k => hb k i i' _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right,
    fun i k k' => ht' k k' i _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right⟩
  refine eq_of_rsT_eq (fun i => V i ⊓ (U k ⊓ U k' ⊓ U k'')) (fun i => inf_le_right)
    (le_iSup_inf hV _) _ _ fun i => ?_
  have e : V i ⊓ (U k ⊓ U k' ⊓ U k'') ≤ U k ⊓ U k' ⊓ U k'' := inf_le_right
  have e1 := (e.trans inf_le_left).trans inf_le_left
  have e2 := (e.trans inf_le_left).trans inf_le_right
  have e3 := e.trans inf_le_right
  simp only [rsT_add]
  rw [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e,
    ht' k k' i _ inf_le_left e1 e2, ht' k' k'' i _ inf_le_left e2 e3, ht' k k'' i _ inf_le_left e1 e3]
  ring

end GlobalTheory.CechMixed
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section


open GlobalTheory.UPel.HT.Hecke.PullInj in
theorem GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro S A A' _ _ _ _ G ψ hA hA' hψ hG Q₁ Q₂ hQ₁ hQ₂ ⟨ρ₁, hρ₁⟩ ⟨σ₁, hσ₁⟩ ⟨ρ₂, hρ₂⟩ ⟨σ₂, hσ₂⟩ ⟨w, hw⟩
  have hP := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S A A' G ψ hψ hG
  have := hP.finite
  have := hP.fin
  have := hP.etale
  have := hP.onto
  have hT := GlobalTheory.LinDescent.locTransitive_of_isGaloisCover hP
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  let π := Hecke.sq2 ψ
  let τ : ↥G × ↥G → ((G2 A).left ⟶ (G2 A).left) :=
    fun h => (Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left
  have hτπ : ∀ c, τ c ≫ π = π := hP.inv
  have hτx : ∀ c x, π (τ c x) = π x := fun c x => congrArg (fun q : (G2 A).left ⟶ (G2 A').left => q x) (hτπ c)

  have hchart : ∀ x : (G2 A).left, ∃ k, x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := fun x => by
    obtain ⟨j₂, h₂⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j₁, h₁⟩ := exists_chart hQ₁ (π x)
    exact ⟨(fun _ => j₂, fun _ => j₁), mem_divPull.2 ⟨h₂, h₁⟩⟩

  let Inv : ↥G × ↥G → Prop := fun c => ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z) k,
    r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ c) z _ (w.s k) = gm r z _ (w.s k)
  have hmul : ∀ a b, Inv a → Inv b → Inv (a * b) := fun a b ha hb Z r z k hk => by
    have e : r ≫ τ (a * b) = (r ≫ τ a) ≫ τ b := by rw [Category.assoc]; exact congrArg (r ≫ ·) (hP.mul a b)
    have hk' : (r ≫ τ a) z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
      have h0 := (mem_divPull (F := π)).1 hk
      refine (mem_divPull (F := π)).2 ?_
      change π (τ a (r z)) ∈ _ ∧ π (τ a (r z)) ∈ _
      rw [hτx]; exact h0
    rw [e, hb Z _ z k hk', ha Z r z k hk]

  let s₀ : (G2 A).left ⟶ A.left := (toUnit (G2 A) ≫ η[A]).left
  have hs₀ : s₀ ≫ A.hom = (G2 A).hom := by
    exact Over.w (toUnit (G2 A) ≫ η[A])

  have axis : ∀ (c : ↥G × ↥G) (e : A.left ⟶ (G2 A).left) (e' : A'.left ⟶ (G2 A').left) (T : A.left ⟶ A.left),
      e ≫ π = ψ.left ≫ e' → e ≫ (G2 A).hom = A.hom → e ≫ τ c = T ≫ e → T ≫ ψ.left = ψ.left → T ≫ A.hom = A.hom →
      (∃ ρ : LB.Gen (Q₁.pull e'), ρ.IsGen) → (∃ ρ : LB.Gen (Q₂.pull e'), ρ.IsGen) → Inv c := by
    rintro c e e' T he heS heT hTψ hTS ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩
    obtain ⟨f, hf⟩ := GlobalTheory.T.generator_translate_ratio_global_unit _ _ π Q₁ Q₂ hQ₁ hQ₂ w hw (τ c) (hτπ c)
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_axis_unit_generators_pullback _ _ _ _ ψ.left e e' π he Q₁ Q₂ hQ₁ hQ₂ w hw r₁ r₂ hr₁ hr₂
    have hTx : ∀ a, ψ.left (T a) = ψ.left a := fun a => congrArg (fun q : A.left ⟶ A'.left => q a) hTψ
    have hex : ∀ a, π (e a) = e' (ψ.left a) := fun a => congrArg (fun q : A.left ⟶ (G2 A').left => q a) he
    have hf1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z), gm (r ≫ e) z ⊤ f = 1 := fun Z r z => by
      obtain ⟨k, hk⟩ := hchart (e (r z))
      have hk' : e ((r ≫ T) z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
        have h0 := (mem_divPull (F := π)).1 hk
        refine (mem_divPull (F := π)).2 ?_
        change π (e (T (r z))) ∈ _ ∧ π (e (T (r z))) ∈ _
        rw [hex, hTx, ← hex]; exact h0
      have h1 := hf Z (r ≫ e) z k hk
      have h2 := hg Z r z k hk
      have h3 := hg Z (r ≫ T) z k hk'
      rw [Category.assoc, heT, ← Category.assoc] at h1
      rw [Category.assoc r T ψ.left, hTψ, gm_top_eq A hA g (r ≫ T) r (by rw [Category.assoc, hTS])] at h3
      rw [← h2, mul_left_inj] at h3
      rw [h3] at h1
      exact (mul_eq_right.1 h1.symm)
    intro Z r z k hk
    have hf' : gm r z ⊤ f = 1 := by
      rw [gm_top_eq (G2 A) hA2 f r (r ≫ s₀ ≫ e) (by rw [Category.assoc, Category.assoc, heS, hs₀]), ← Category.assoc]
      exact hf1 Z (r ≫ s₀) z
    rw [hf Z r z k hk, hf', _root_.one_mul]
  have inv₁ : ∀ h : ↥G, Inv (1, h) := fun h =>
    axis (1, h) (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : A' ⟶ A') (𝟙 A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_left ψ))
      (Over.w _)
      (by
        show (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (Hecke.transl (lift ((1 : ↥G) : 𝟙_ (Over S) ⟶ A) h.1)).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₁ A h.1))
      (hG.inv h) (Over.w _) ⟨ρ₁, hρ₁⟩ ⟨ρ₂, hρ₂⟩
  have inv₂ : ∀ h : ↥G, Inv (h, 1) := fun h =>
    axis (h, 1) (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 A') (1 : A' ⟶ A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_right ψ))
      (Over.w _)
      (by
        show (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (Hecke.transl (lift h.1 ((1 : ↥G) : 𝟙_ (Over S) ⟶ A))).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₂ A h.1))
      (hG.inv h) (Over.w _) ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  have inv : ∀ c, Inv c := fun c => by
    have e : c = (c.1, 1) * (1, c.2) := Prod.ext (_root_.mul_one c.1).symm (_root_.one_mul c.2).symm
    rw [e]
    exact hmul _ _ (inv₂ c.1) (inv₁ c.2)

  have hdesc : ∀ p : Q₂.ι × Q₁.ι, ∃ g : Γ((G2 A').left, Q₂.U p.1 ⊓ Q₁.U p.2)ˣ, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (G2 A).left) (z : Z), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) →
      gm (r ≫ π) z _ g = gm r z _ (w.s (fun _ => p.1, fun _ => p.2)) := fun p => by
    obtain ⟨g, hg⟩ := GlobalTheory.LinDescent.LocTransitive.exists_descend_unit hT (Q₂.U p.1 ⊓ Q₁.U p.2)
      (κ := Unit) (fun _ => (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2))
      (fun _ x hx => (mem_divPull (F := π)).1 hx)
      (fun x hx => ⟨(), (mem_divPull (F := π)).2 hx⟩)
      (fun _ => w.s (fun _ => p.1, fun _ => p.2)) (fun _ _ _ _ _ => rfl)
      (fun c Z r z hz => by
        have hz' : r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
          (mem_divPull (F := π)).2 hz
        refine ⟨(), (), hz', ?_, inv c Z r z _ hz'⟩
        refine (mem_divPull (F := π)).2 ?_
        change π (τ c (r z)) ∈ _ ∧ π (τ c (r z)) ∈ _
        rw [hτx]; exact hz)
    exact ⟨g, fun Z r z hz => hg Z r z () hz⟩
  choose g hg using hdesc
  refine ⟨⟨g⟩, fun p q => ?_⟩
  apply GlobalTheory.LinDescent.unit_ext_of_flat (π := π)
  intro x hx
  have hp : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
    (mem_divPull (F := π)).2 hx.1
  have hq : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => q.1, fun _ => q.2) :=
    (mem_divPull (F := π)).2 hx.2
  have e1 := gen_germ hw (𝟙 _) x hp hq
  rw [germ_div_g _ _ (𝟙 _) x hp hq, gm_pull_g Q₂ π (𝟙 _) x hx.1.1 hx.2.1,
    gm_pull_g Q₁ π (𝟙 _) x hx.1.2 hx.2.2] at e1
  refine ((gm_res (𝟙 _ ≫ π) x inf_le_left hx (g p)).trans (hg p _ (𝟙 _) x hp)).trans ?_
  rw [e1, map_mul, gm_res (𝟙 _ ≫ π) x inf_le_right hx (g q), germ_div_g Q₂ Q₁ (𝟙 _ ≫ π) x hx.1 hx.2]
  exact congrArg (_ * ·) (hg q _ (𝟙 _) x hq).symm
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

theorem _root_.GlobalTheory.T.constantCoeff_iterate_invariant_derivation_linear : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → (∀ i, swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ r : R, constantCoeff ((invDer μ u)^[p] F) - ∑ j, constantCoeff ((invDer μ u)^[p] (X j)) * coeff (Finsupp.single j 1) F = p * r := by
  first | exact @GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear | exact GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear | (intros; apply GlobalTheory.LawDer.constantCoeff_iterate_invDer_sub_linear <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.MVFree

theorem shortExact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ (w : biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f))))))) ≫ biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A'))))) = 0), (ShortComplex.mk _ _ w).ShortExact := by
  intro R _ A A' _ _ _ _ f hN w
  obtain ⟨h1, h2⟩ := hN
  obtain ⟨w', hex⟩ := GlobalTheory.T.etale_mayerVietoris_free_sequence_exact R A A' f h1 h2
  have hm := GlobalTheory.T.mono_free_etale_mayerVietoris_left_map R A A' f
  have he := GlobalTheory.T.etaleMayerVietoris_free_right_epi R A A' f h1 h2
  exact { exact := hex, mono_f := hm, epi_g := he }

end GlobalTheory.EtC.MVFree
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.low_rank_box_function_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | exact GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan <;> assumption)
end
