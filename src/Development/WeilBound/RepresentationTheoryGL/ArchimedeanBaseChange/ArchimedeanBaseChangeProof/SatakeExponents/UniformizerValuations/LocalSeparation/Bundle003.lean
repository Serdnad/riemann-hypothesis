module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ParabolicInductionCongr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.LocalL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

theorem tso_map_heckeVec {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G X} {K : Subgroup G} {h : G → ℂ} (hK : IsCommensurated K)
    (hh : h ∈ Hecke ℂ K) (L : V →ₗ[ℂ] X) {x : V} (hL : ∀ g, L (ρ g x) = τ g (L x)) :
    L (heckeVec ρ K h x) = heckeVec τ K h (L x) := by
  refine (L.toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ x)).trans (finsum_congr fun c => ?_)
  simp [hL]

theorem tso_heckeVec_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} (S : Submodule ℂ V) (hS : ∀ g, ∀ y ∈ S, ρ g y ∈ S) {x : V} (hx : x ∈ S) :
    heckeVec ρ K h x ∈ S := by
  unfold heckeVec
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun c => S.smul_mem _ (hS _ _ hx)

theorem tso_heckeVec_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {h : G → ℂ} : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

theorem treeSatOf_holds : TreeSatOf := by
  intro hT E _ _ _ N t P w hg hu htp ⟨φ0, hφ0S, hφ00, hφ0K⟩
  obtain ⟨hinv, J, L, heq, hsep⟩ := hT E N t P w hg hu htp
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w N).1
  have hKc := Final.GLintComm E w N
  have fixK : ∀ φ, (∀ k ∈ KGL w (n := N), finRep E N (locGL E N w k) φ = φ) →
      φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) :=
    fun φ h => GlobalTheory.LGrp.mem_fixed.2 fun k hk => h k hk
  have smK : ∀ φ, φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) → SmVec ((finRep E N).comp (locGL E N w)) φ :=
    fun φ h => ⟨_, hKo, h⟩
  have hLfix : ∀ j φ, φ ∈ t.space → φ ∈ fixed ((finRep E N).comp (locGL E N w)) (KGL w (n := N)) →
      L j φ ∈ fixed (lp P w) (KGL w (n := N)) := fun j φ hS hf =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← heq j k φ hS (smK _ hf), GlobalTheory.LGrp.mem_fixed.1 hf k hk]
  obtain ⟨j, hj⟩ : ∃ j, L j φ0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hφ00 (hsep φ0 hφ0S (smK _ (fixK _ hφ0K)) hc)
  obtain ⟨b, hb, -⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ) (fun i => (P.σ i w).smooth)
    (fun i => (P.σ i w).irred) (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj
  have hvec : ∀ f ∈ fixed (lp P w) (KGL w (n := N)), f ≠ 0 → IsSatVecGL w (lp P w) f (∑ i, b i) := fun f hf hf0 => by
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd P.h (π := fun i => (P.σ i w).ρ)
      (fun i => (P.σ i w).smooth) (fun i => (P.σ i w).irred) hf hf0
    have e : S = b := funext fun a => (hS a).unique (hb a)
    rw [← e]
    exact hfS
  have hcard : (∑ i, b i).card = N := (hvec _ (hLfix j φ0 hφ0S (fixK _ hφ0K)) hj).2.2.1
  refine ⟨_, ⟨b, fun i => ⟨(hb i).1, hb i⟩, rfl⟩, fun φ hφS hφ0 hφK => ?_⟩
  have hf := fixK _ hφK
  refine ⟨hφ0, hf, hcard, fun ϖ hϖ i hi => ?_⟩
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := N) hϖ i
  have hTS := tso_heckeVec_mem (K := KGL w (n := N)) (h := Tj ℂ N (Ov E w) ϖ i) t.space hinv hφS
  have hTf := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed hKc hh hf
  refine sub_eq_zero.1 (hsep _ (t.space.sub_mem hTS (t.space.smul_mem _ hφS))
    (smK _ (sub_mem hTf (Submodule.smul_mem _ _ hf))) fun j' => ?_)
  have key := tso_map_heckeVec (τ := lp P w) hKc hh (L j') fun g => heq j' g φ hφS (smK _ hf)
  rw [LinearMap.map_sub, LinearMap.map_smul]
  refine sub_eq_zero.2 (key.trans ?_)
  by_cases h0 : L j' φ = 0
  · exact (congrArg (heckeVec (lp P w) (KGL w (n := N)) (Tj ℂ N (Ov E w) ϖ i)) h0).trans
      (tso_heckeVec_zero.trans ((smul_zero _).symm.trans (congrArg _ h0.symm)))
  · exact (hvec _ (hLfix j' φ hφS hf) h0).2.2.2 ϖ hϖ i hi

end PositivityTheory.Rg.BcB.F.RS

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_zero' {N : ℕ} (V : Submodule ℂ (Sm E N)) : tw V 0 = V := by
  unfold tw
  have h : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
    apply Subtype.ext; ext x
    simp [GlobalTheory.CuspRep.Model.absC, GlobalTheory.Mem.Chr.CharModel.absHom]
  rw [h]
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twPart_one (x : Σ M : ℕ, Submodule ℂ (Sm E M)) : twPart 1 x = x := by
  obtain ⟨M, V⟩ := x
  simp only [twPart]
  congr 1
  convert Submodule.map_id V
  ext φ x
  simp [mulChi, chiDet]

theorem twRep_of_one {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (hχ : ∀ g, χ g = 1) : twRep ρ χ = ρ := by
  ext g x
  simp [twRep_apply, hχ]

theorem Sep.equiv {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ.Equiv τ') : Sep ρ S τ' := by
  obtain ⟨hS, J, L, hL, hinj⟩ := h
  refine ⟨hS, J, fun j => e.toLinearMap ∘ₗ L j, fun j g x hx hs => ?_, fun x hx hs h0 => hinj x hx hs fun j => ?_⟩
  · simp only [LinearMap.comp_apply, hL j g x hx hs]
    exact LinearMap.congr_fun (e.isIntertwining' g) (L j x)
  · exact e.toLinearEquiv.injective ((h0 j).trans (map_zero _).symm)

theorem Sep.equiv_symm {G V X Y : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : AddCommGroup Y} {_ : Module ℂ Y} {ρ : Representation ℂ G V} {S : Submodule ℂ V}
    {τ : Representation ℂ G X} {τ' : Representation ℂ G Y} (h : Sep ρ S τ) (e : τ'.Equiv τ) : Sep ρ S τ' :=
  h.equiv e.symm

theorem sep_of_subsingleton {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] (ρ : Representation ℂ G V) (S : Submodule ℂ V) (τ : Representation ℂ G X) (hG : ∀ g : G, g = 1)
    (hX : Nontrivial X) (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ x ∈ S, ℓ x = 0 → x = 0) : Sep ρ S τ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  refine ⟨fun g x hx => by rw [hG g, map_one]; exact hx, Unit, fun _ => ℓ.smulRight v,
    fun _ g x _ _ => by rw [hG g, map_one, map_one]; rfl,
    fun x hx _ h0 => hℓ x hx ((smul_eq_zero.1 (h0 ())).resolve_right hv)⟩

theorem equiv_untwist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (f : a ⊕ b ≃ n)
    {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GL n k) Z) (π₁ : Representation ℂ (GL a k) X) (π₂ : Representation ℂ (GL b k) Y)
    (χ₁ : GL a k →* ℂˣ) (χ₂ : GL b k →* ℂˣ) (h₁ : ∀ g, χ₁ g = 1) (h₂ : ∀ g, χ₂ g = 1)
    (e : τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor (twRep π₁ χ₁) (twRep π₂ χ₂)))) :
    Nonempty (τ.Equiv (GlobalTheory.SmGL.ind₂ f (GlobalTheory.SmGL.extTensor π₁ π₂))) := by
  rw [twRep_of_one π₁ χ₁ h₁, twRep_of_one π₂ χ₂ h₂] at e
  exact ⟨e⟩

theorem sep_rank0 (w : Pl E) (S : Submodule ℂ (Sm E 0)) (P : Pre E 0) :
    Sep ((finRep E 0).comp (locGL E 0 w)) S (lp P w) := by
  refine sep_of_subsingleton _ _ _ (fun g => Units.ext (Subsingleton.elim _ _))
    (GlobalTheory.PfBCI.nontrivial_locProd P.h w (P.σ · w)) ((LinearMap.proj 1).comp (Sm E 0).subtype) ?_
  intro x _ h
  apply Subtype.ext; funext g
  obtain rfl : g = 1 := Units.ext (Subsingleton.elim _ _)
  exact h

theorem sep_leaf_pos (hL : LeafMod) (w : Pl E) {M : ℕ} (V : Submodule ℂ (Sm E M)) (hV : IsDiscrete V) (hM : 0 < M)
    (P : Pre E M) (hp : TreeParts (Tr.leaf V 0) P) : Sep ((finRep E M).comp (locGL E M w)) V (lp P w) := by
  obtain ⟨c, N, h, V', σ, m, pos, disc, loc, inf⟩ := P
  have hp' : List.ofFn (fun i => (⟨N i, V' i⟩ : Σ M, Submodule ℂ (Sm E M))) = [⟨M, V⟩] := by
    unfold TreeParts at hp
    rw [hp]
    simp [Tr.leafList, hM]
  have hc : c = 1 := by simpa using congrArg List.length hp'
  subst hc
  obtain ⟨d, rfl⟩ : ∃ d, N = fun _ => d := ⟨N 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s, rfl⟩ : ∃ s, σ = fun _ => s := ⟨σ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have h0 : (⟨d, V' 0⟩ : Σ M, Submodule ℂ (Sm E M)) = ⟨M, V⟩ := by simpa using hp'
  obtain ⟨rfl, hVV⟩ := Sigma.mk.inj_iff.1 h0
  obtain rfl := eq_of_heq hVV
  obtain ⟨e⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (s w).smooth (GlobalTheory.SmGL.stdBlocks (fun _ => d) h)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val, Subsingleton.elim a 0]; simp))
  exact Sep.equiv (hL E d (V' 0) w (s w) (disc 0) (loc 0 w)) e

theorem sum_leafList : ∀ {N : ℕ} (t : Tr E N), ((t.leafList.filter fun x => 0 < x.1).map (·.1)).sum = N
  | M, .leaf V z => by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp [Tr.leafList]
    · simp [Tr.leafList, h]
  | _, .node t₁ t₂ => by simp [Tr.leafList, List.filter_append, sum_leafList t₁, sum_leafList t₂]

def Pre.restr {n : ℕ} (P : Pre E n) {k r : ℕ} (ι : Fin k → Fin P.c) (h : ∑ i, P.N (ι i) = r) : Pre E r where
  c := k
  N i := P.N (ι i)
  h := h
  V i := P.V (ι i)
  σ i := P.σ (ι i)
  m i := P.m (ι i)
  pos i := P.pos _
  discrete i := P.discrete _
  loc i := P.loc _
  inf i := P.inf _

theorem exists_split {n r s : ℕ} (P : Pre E n) (A B : List (Σ M : ℕ, Submodule ℂ (Sm E M))) (hAB : parts P = A ++ B)
    (hA : (A.map (·.1)).sum = r) (hB : (B.map (·.1)).sum = s) :
    ∃ (P₁ : Pre E r) (P₂ : Pre E s), parts P₁ = A ∧ parts P₂ = B := by
  have hlen : P.c = A.length + B.length := by simpa [parts] using congrArg List.length hAB
  have key : ∀ k (hk : k < P.c), (⟨P.N ⟨k, hk⟩, P.V ⟨k, hk⟩⟩ : Σ M, Submodule ℂ (Sm E M)) =
      (A ++ B)[k]'(by simp; omega) := fun k hk => by
    have := List.getElem_of_eq hAB (i := k) (by simp [parts]; exact hk)
    simpa [parts] using this
  let ι₁ : Fin A.length → Fin P.c := fun i => ⟨i, by omega⟩
  let ι₂ : Fin B.length → Fin P.c := fun j => ⟨A.length + j, by omega⟩
  have e₁ : List.ofFn (fun i => (⟨P.N (ι₁ i), P.V (ι₁ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = A := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    exact (key k _).trans (List.getElem_append_left hk2)
  have e₂ : List.ofFn (fun i => (⟨P.N (ι₂ i), P.V (ι₂ i)⟩ : Σ M, Submodule ℂ (Sm E M))) = B := by
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    rw [List.getElem_ofFn]
    refine (key _ _).trans ?_
    rw [List.getElem_append_right (by omega)]
    simp
  have s₁ : ∑ i, P.N (ι₁ i) = r := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₁
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hA, ← this]; rfl
  have s₂ : ∑ i, P.N (ι₂ i) = s := by
    have := congrArg (fun l => (l.map (·.1)).sum) e₂
    simp only [List.map_ofFn, List.sum_ofFn] at this
    rw [← hB, ← this]; rfl
  exact ⟨Pre.restr P ι₁ s₁, Pre.restr P ι₂ s₂, e₁, e₂⟩

theorem tree_module_separation (hL : LeafMod) (hN : NodeMod) (hJ : JoinMod) (w : Pl E) :
    ∀ {N : ℕ} (t : Tr E N) (P : Pre E N), t.Good → t.Untw → TreeParts t P →
      Sep ((finRep E N).comp (locGL E N w)) t.space (lp P w) := by
  intro N t
  induction t with
  | leaf V z =>
    intro P hg hu hp
    have hz : z = 0 := hu z (by simp [Tr.twists])
    subst hz
    show Sep _ (tw V 0) _
    rw [tw_zero']
    rcases hg with ⟨hM, -, -⟩ | ⟨hM, hV, -⟩
    · subst hM; exact sep_rank0 w V P
    · exact sep_leaf_pos hL w V hV hM P hp
  | node t₁ t₂ ih₁ ih₂ =>
    intro P hg hu hp
    obtain ⟨g₁, g₂⟩ := hg
    have u₁ : t₁.Untw := fun z hz => hu z (List.mem_append_left _ hz)
    have u₂ : t₂.Untw := fun z hz => hu z (List.mem_append_right _ hz)
    have hp' : parts P = (t₁.leafList.filter fun x => 0 < x.1) ++ (t₂.leafList.filter fun x => 0 < x.1) := by
      rw [← List.filter_append]; exact hp
    obtain ⟨P₁, P₂, h₁, h₂⟩ := exists_split P _ _ hp' (sum_leafList t₁) (sum_leafList t₂)
    have hj : IsJoin 1 1 P₁ P₂ P := by
      unfold IsJoin
      rw [hp', h₁, h₂]
      have : twPart (E := E) 1 = id := funext twPart_one
      rw [this, List.map_id, List.map_id]
    obtain ⟨e⟩ := equiv_untwist (e := (hJ E _ _ _ rfl 1 1 P₁ P₂ P w hj).some)
      (h₁ := fun _ => by simp [HChar.loc])
      (h₂ := fun _ => by simp [HChar.loc])
    exact Sep.equiv_symm (hN E _ _ t₁ t₂ w _ _ _ _ (ih₁ P₁ g₁ u₁ h₁) (ih₂ P₂ g₂ u₂ h₂)) e

theorem treeModOf_holds : TreeModOf :=
  fun hL hN hJ _ _ _ _ _ t P w hg hu hp => tree_module_separation hL hN hJ w t P hg hu hp

end PositivityTheory.Rg.BcB.F.RS

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS.JB

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twCongr' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twRep ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (φ v)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (φ.isIntertwining' g) v

unseal Iso i2 in
theorem fin_step {r t N : ℕ} (h : r + t = N) {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] (ρ₀ : Representation ℂ (GL (Fin N) k) V₀) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁)
    (ρ₂ : Representation ℂ (GL (Fin t) k) V₂) (A₀ : RB k N) (A : RB k r) (B : RB k t) (e₀ : Nonempty (ρ₀.Equiv A₀.ρ))
    (e₁ : Nonempty (ρ₁.Equiv A.ρ)) (e₂ : Nonempty (ρ₂.Equiv B.ρ)) (hI : Iso A₀ (i2 h A B)) :
    Nonempty (ρ₀.Equiv (ind₂ (stdSum h) (extTensor ρ₁ ρ₂))) := by
  have a : Nonempty (A₀.ρ.Equiv (ind₂ (stdSum h) (extTensor A.ρ B.ρ))) := hI
  exact e₀.elim fun x => a.elim fun y => (ind₂_congr h e₁ e₂).elim fun z => ⟨(x.trans y).trans z.symm⟩

unseal mp in
theorem to_mp {c N : ℕ} (z : Fin c → IrrGL (k := k)) (h : ∑ a, (z a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (e : Nonempty (ρ.Equiv (prodIrr z h))) :
    Nonempty (ρ.Equiv (mp z (stdBlocks (fun a => (z a).1) h)).ρ) := e

end Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locComp_unique' {a : ℕ} {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))} (h : IsLocCompGL V w σ)
    (h' : IsLocCompGL V w σ') : Nonempty (σ.ρ.Equiv σ'.ρ) := by
  have hst : ∀ g, ∀ φ ∈ V, finRep E a (locGL E a w g) φ ∈ V := fun g φ hφ => hV.stable (.fin _) φ hφ
  let ρV : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
    { toFun := fun g => (finRep E a (locGL E a w g)).restrict (hst g)
      map_one' := LinearMap.ext fun φ => Subtype.ext (by simp)
      map_mul' := fun g g' => LinearMap.ext fun φ => Subtype.ext (by simp) }
  have := σ.irred
  have := σ'.irred
  obtain ⟨f', h0', h1', h2'⟩ := h'
  refine LocUniq.equiv_of_isoPart σ.ρ σ'.ρ ρV ?_ ⟨f'.codRestrict V h1', fun g => LinearMap.ext fun v =>
    Subtype.ext (h2' g v)⟩ fun e => h0' (LinearMap.ext fun v => by
      have := congrArg (fun F : σ'.ρ.IntertwiningMap ρV => (F.toLinearMap v : Sm E a)) e
      simpa using this)
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x.1 ∈ ⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1 := by
    rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w σ h]; exact x.2
  have hle : (⨆ f : GlobalTheory.LocDual.Maps V w σ, LinearMap.range f.1) ≤
      (LocUniq.isoPart σ.ρ ρV).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, Submodule.mem_iSup_of_mem (⟨f.1.codRestrict V f.2.1, fun g => LinearMap.ext fun u =>
      Subtype.ext (f.2.2 g u)⟩ : σ.ρ.IntertwiningMap ρV) ⟨v, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

theorem of_eq_of_locComp' {w : HeightOneSpectrum (𝓞 E)} {x y : Σ M : ℕ, Submodule ℂ (Sm E M)}
    (hxy : x = y) (hV : IsDiscrete x.2) (σ : SmIrr (GL (Fin x.1) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin y.1) (w.adicCompletion E))) (h : IsLocCompGL x.2 w σ) (h' : IsLocCompGL y.2 w σ') :
    IrrGL.of σ.ρ σ.smooth σ.irred = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  subst hxy
  exact IrrGL.of_eq_of.2 (locComp_unique' hV h h')

def twLoc {w : HeightOneSpectrum (𝓞 E)} {M : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin M) (w.adicCompletion E)) V) (χ : HChar E) :
    (twRep ρ (CuspSub.locDet M χ w)).Equiv (twist ρ (GlobalTheory.SmGL.detChar (Fin M) (χ.loc w))) :=
  .mk (LinearEquiv.refl ℂ V) fun _ => LinearMap.ext fun _ => rfl

def twCls {m : ℕ} (χ : HChar E) (P : Pre E m) (w : HeightOneSpectrum (𝓞 E)) :
    Fin P.c → IrrGL (k := w.adicCompletion E) :=
  fun j => (P.cls j w).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w)

theorem cls_tw {n M : ℕ} (D : Pre E n) (i : Fin D.c) (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)}
    (V : Submodule ℂ (Sm E M)) (σ : SmIrr (GL (Fin M) (w.adicCompletion E))) (hσ : IsLocCompGL V w σ)
    (hi : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) = twPart χ ⟨M, V⟩) :
    D.cls i w = (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ.loc w) (ParLaws.isSmoothChar_loc χ w) := by
  rw [IrrGL.tw_of]
  have h1 := of_eq_of_locComp' hi (D.discrete i) (D.σ i w)
    (σ.twist (CuspSub.locDet M χ w) (CuspSub.isOpen_ker_locDet χ w)) (D.loc i w)
    (TwistDisc.isLocCompGL_map χ hσ)
  exact h1.trans (IrrGL.of_eq_of.2 ⟨twLoc σ.ρ χ⟩)

theorem join_parts {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n}
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) : ∃ hc : D.c = Pa.c + Pb.c, ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i := by
  have e : List.ofFn (fun i => (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M))) =
      List.ofFn (Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩)) := by
    have hJ' : parts D = (parts Pa).map (twPart χ₁) ++ (parts Pb).map (twPart χ₂) := hJ
    unfold parts at hJ'
    rw [hJ', List.map_ofFn, List.map_ofFn, List.ofFn_fin_append]
    rfl
  obtain ⟨hc, hf⟩ := Sigma.mk.inj_iff.1 (List.ofFn_inj'.1 e)
  exact ⟨hc, fun i => (Fin.heq_fun_iff hc).1 hf (Fin.cast hc.symm i)⟩

theorem cls_append {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hc : D.c = Pa.c + Pb.c) (hD : ∀ i : Fin (Pa.c + Pb.c),
      (⟨D.N (Fin.cast hc.symm i), D.V (Fin.cast hc.symm i)⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) =
        Fin.append (fun j => twPart χ₁ ⟨Pa.N j, Pa.V j⟩) (fun j => twPart χ₂ ⟨Pb.N j, Pb.V j⟩) i) :
    ∀ i, Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w := by
  intro i
  refine Fin.addCases (motive := fun i =>
    Fin.append (twCls χ₁ Pa w) (twCls χ₂ Pb w) i = D.cls (Fin.cast hc.symm i) w) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have hi := hD (Fin.castAdd Pb.c j)
    rw [Fin.append_left] at hi
    exact (cls_tw D _ χ₁ (Pa.V j) (Pa.σ j w) (Pa.loc j w) hi).symm
  · rw [Fin.append_right]
    have hi := hD (Fin.natAdd Pa.c j)
    rw [Fin.append_right] at hi
    exact (cls_tw D _ χ₂ (Pb.V j) (Pb.σ j w) (Pb.loc j w) hi).symm

theorem twist_lp {a : ℕ} (χ : HChar E) (P : Pre E a) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((twRep (lp P w) ((χ.loc w).comp GeneralLinearGroup.det)).Equiv (prodIrr (twCls χ P w) P.h)) :=
  ⟨(twCongr' (prodIrrEquiv P.h (fun j => (P.σ j w).ρ) (fun j => (P.σ j w).smooth)
    fun j => (P.σ j w).irred) _).trans
    (prodIrrTwistEquiv (fun j => P.cls j w) P.h (χ.loc w) (ParLaws.isSmoothChar_loc χ w))⟩

theorem lp_equiv {n : ℕ} (D : Pre E n) (w : HeightOneSpectrum (𝓞 E)) :
    Nonempty ((lp D w).Equiv (prodIrr (fun i => D.cls i w) D.h)) :=
  ⟨prodIrrEquiv D.h (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) fun i => (D.σ i w).irred⟩

theorem cls_list {n a b : ℕ} {χ₁ χ₂ : HChar E} {Pa : Pre E a} {Pb : Pre E b} {D : Pre E n} (w : HeightOneSpectrum (𝓞 E))
    (hJ : IsJoin χ₁ χ₂ Pa Pb D) :
    List.ofFn (fun i => D.cls i w) = List.ofFn (twCls χ₁ Pa w) ++ List.ofFn (twCls χ₂ Pb w) := by
  obtain ⟨hc, hD⟩ := join_parts hJ
  rw [← List.ofFn_fin_append, List.ofFn_congr hc]
  exact congrArg List.ofFn (funext fun i => (cls_append w hc hD i).symm)

theorem joinMod_holds : JoinMod := fun _ _ _ _ _ _ _ h χ₁ χ₂ Pa Pb D w hJ =>
  fin_step h _ _ _ _ _ _ (to_mp (fun i => D.cls i w) D.h _ (lp_equiv D w))
    (to_mp (twCls χ₁ Pa w) Pa.h _ (twist_lp χ₁ Pa w)) (to_mp (twCls χ₂ Pb w) Pb.h _ (twist_lp χ₂ Pb w))
    (stagesB _ _ _ _ _ _ (cls_list w hJ) h _ _ _)

end PositivityTheory.Rg.BcB.F.RS.JB

end
end
