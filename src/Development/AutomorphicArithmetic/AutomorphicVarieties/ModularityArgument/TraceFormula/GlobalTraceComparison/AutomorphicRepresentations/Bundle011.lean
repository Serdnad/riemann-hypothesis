module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle006
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle002
public import GroundTheory.AutomorphicForms.AdelicGLn
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem exists_core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K M : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hMo : IsOpen (M : Set G)) (hMK : M ≤ K) :
    ∃ C : Subgroup G, IsOpen (C : Set G) ∧ C ≤ M ∧ ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set M' : Subgroup K := M.subgroupOf K with hM'
  have hM'o : IsOpen (M' : Set K) := hMo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ M') := Subgroup.quotient_finite_of_isOpen M' hM'o
  haveI : M'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcl : IsClosed (M'.normalCore : Set K) := by
    have hc : IsClosed (M' : Set K) := Subgroup.isClosed_of_isOpen M' hM'o
    have : (M'.normalCore : Set K) = ⋂ b : K, (fun a : K => b * a * b⁻¹) ⁻¹' (M' : Set K) := by
      ext a
      simp [Subgroup.normalCore, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun b => hc.preimage (by fun_prop)
  have hop : IsOpen (M'.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨M'.normalCore.map K.subtype, ?_, ?_, ?_⟩
  · have : ((M'.normalCore.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (M'.normalCore : Set K) := by
      ext x; simp
    rw [this]
    exact hKo.isOpenMap_subtype_val _ hop
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ M' := Subgroup.normalCore_le M' ha
    exact h1
  · rintro k hk _ ⟨a, ha, rfl⟩
    refine ⟨⟨k, hk⟩ * a * (⟨k, hk⟩ : K)⁻¹, ?_, by simp⟩
    exact (Subgroup.normalCore_normal M').conj_mem a ha _

private theorem hecke_slice {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (K' : Subgroup (GLw n w × GLw 0 w)) (f : GLw n w × GLw 0 w → ℂ) (hf : IsHecke K' f)
    (N : Subgroup (GLw n w)) (hN : ∀ k ∈ N, ((k, 1) : GLw n w × GLw 0 w) ∈ K') :
    IsHecke N (fun g => f (g, 1)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · haveI : Unique (GLw 0 w) := Unique.mk' _
    have e : (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) =
        ⇑(Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm := by
      funext g
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have h : Topology.IsClosedEmbedding (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) := by
      rw [e]
      exact (Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm.isClosedEmbedding
    exact hf.1.comp_isClosedEmbedding h
  · have h := hf.2 _ (hN k hk) (x, 1)
    simpa using h

theorem lcLevel_pf : LcLevel := by
  classical
  intro E _ _ _ n Z N₀ hN₀ φ₁ φ₂ hφ
  have hK := fun w : Pl E => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have key : ∀ w ∈ Z, ∃ C : Subgroup (GLw n w), IsOpen (C : Set (GLw n w)) ∧ C ≤ N₀ w ∧
      (∀ k ∈ KGL w (n := n), ∀ x ∈ C, k * x * k⁻¹ ∈ C) ∧ ∀ b, IsHecke C (two φ₁ φ₂ w b) := by
    intro w hw
    obtain ⟨⟨A, hAo, -, hA⟩, ⟨B, hBo, -, hB⟩⟩ := hφ w hw
    let ι : GLw n w →* GLw n w × GLw 0 w := MonoidHom.inl _ _
    have hι : Continuous ι := continuous_id.prodMk continuous_const
    have hMo : IsOpen ((N₀ w ⊓ A.comap ι ⊓ B.comap ι : Subgroup (GLw n w)) : Set (GLw n w)) :=
      ((hN₀ w).1.inter (hAo.preimage hι)).inter (hBo.preimage hι)
    obtain ⟨C, hCo, hCM, hCn⟩ := exists_core (KGL w (n := n)) (N₀ w ⊓ A.comap ι ⊓ B.comap ι) (hK w).1 (hK w).2
      hMo (fun x hx => (hN₀ w).2.1 hx.1.1)
    refine ⟨C, hCo, fun x hx => (hCM hx).1.1, hCn, ?_⟩
    rintro (_ | _)
    · exact hecke_slice w A (φ₁ w) hA C fun k hk => (hCM hk).1.2
    · exact hecke_slice w B (φ₂ w) hB C fun k hk => (hCM hk).2
  choose! C hC using key
  refine ⟨fun w => if w ∈ Z then C w else N₀ w, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      obtain ⟨a, b, c, -⟩ := hC w hw
      exact ⟨a, b.trans (hN₀ w).2.1, c, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact hN₀ w
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact (hC w hw).2.1
    · simp only [if_neg hw]
      exact le_rfl
  · intro w hw b
    simp only [if_pos hw]
    exact (hC w hw).2.2.2 b

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abstract

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

private theorem list_eig (L : ι → Module.End ℂ M) (c : ι → ℂ) (x : M) (l : List ι)
    (h : ∀ i ∈ l, L i x = c i • x) : (l.map L).prod x = (l.map c).prod • x :=
  _root_.UpperTheory.Reformulated.B.Qk12.list_eig L c x l h

private theorem prod_split [DecidableEq ι] (L : ι → Module.End ℂ M) (I₀ I₁ : Finset ι) (hd : Disjoint I₀ I₁)
    (hc : ∀ i ∈ I₀ ∪ I₁, ∀ k ∈ I₀ ∪ I₁, i ≠ k → Commute (L i) (L k)) :
    ((I₀ ∪ I₁).toList.map L).prod = (I₀.toList.map L).prod * (I₁.toList.map L).prod := by
  have hp : (I₀ ∪ I₁).toList.Perm (I₀.toList ++ I₁.toList) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 ?_
    · exact List.nodup_append.2 ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab =>
        Finset.disjoint_left.1 hd (Finset.mem_toList.1 ha) (hab ▸ Finset.mem_toList.1 hb)⟩
    · intro a
      simp
  have hq := hp.map L
  rw [hq.prod_eq' ?_, List.map_append, List.prod_append]
  rw [List.pairwise_map]
  exact (Finset.nodup_toList _).imp_of_mem fun ha hb hab =>
    hc _ (Finset.mem_toList.1 ha) _ (Finset.mem_toList.1 hb) hab

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem two_in {Z T T' : Finset (Pl E)} {w : Pl E} (hw : w ∈ Z) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T' φ₂ e₂) w b = two φ₁ φ₂ w b := by
  cases b <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw]

private theorem slot_pair_functions_eq {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∈ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w false = (fun g => fn2 n 0 w (e₁ w) (g, 1)) ∧
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w true = (fun g => fn2 n 0 w (e₂ w) (g, 1)) := by
  constructor <;> funext g <;> simp [two, intersection_update_fsHerm_neg_one, hw, hT]

private theorem two_off {Z T : Finset (Pl E)} {w : Pl E} (hw : w ∉ Z) (hT : w ∉ T) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (b : Bool) :
    two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) w b = (KGL w (n := n) : Set (GLw n w)).indicator 1 := by
  have key : ∀ g : GLw n w, (K2 n 0 w : Set (GLw n w × GLw 0 w)).indicator (1 : GLw n w × GLw 0 w → ℂ) (g, 1) =
      (KGL w (n := n) : Set (GLw n w)).indicator 1 g := by
    intro g
    by_cases hg : g ∈ KGL w (n := n)
    · rw [Set.indicator_of_mem, Set.indicator_of_mem] <;> simp [hg, K2, Subgroup.mem_prod]
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem] <;> simp [hg, K2, Subgroup.mem_prod]
  cases b <;> funext g <;> simpa [two, intersection_update_fsHerm_neg_one, hw, hT] using key g

private def slots (S : Set (Pl E)) (Z T : Finset (Pl E)) : Finset (Pl E × Bool) :=
  Z ×ˢ Finset.univ ∪ (T ×ˢ Finset.univ).filter (Sl S)

private theorem fam_positions (hEx : Ex2Act) {S : Set (Pl E)} {Z : Finset (Pl E)} {N : ∀ w : Pl E, Subgroup (GLw n w)}
    (hZ : SplitIn S Z) (hG : Good Z N) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w)
    (hφ : ∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) (T : Finset (Pl E)) (hT : Disjoint T Z)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) :
    Fam S N (slots S Z T) (two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.1 hi with h | h
    · have hw := (Finset.mem_product.1 h).1
      refine ⟨⟨(hZ _ hw).1, fun _ => (hZ _ hw).2⟩, ?_⟩
      rw [two_in hw]
      exact hφ _ hw _
    · obtain ⟨h1, hs⟩ := Finset.mem_filter.1 h
      have hwT := (Finset.mem_product.1 h1).1
      have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hT hwT
      refine ⟨hs, ?_⟩
      rw [(hG i.1).2.2.2 hwZ]
      obtain ⟨w, b⟩ := i
      cases b
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1]
        exact (hEx E n w (e₁ w)).1
      · rw [(slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2]
        exact (hEx E n w (e₂ w)).1
  · intro i hs hi
    have hwZ : i.1 ∉ Z := fun h => hi (Finset.mem_union_left _ (Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩))
    have hwT : i.1 ∉ T := fun h => hi (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h, Finset.mem_univ _⟩, hs⟩))
    rw [two_off hwZ hwT, (hG i.1).2.2.2 hwZ]

private def cv (B : Pl E → Multiset ℂˣ) (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (i : Pl E × Bool) : ℂ :=
  if i.2 then ev2 n 0 i.1 (e₂ i.1) (inv (B (cPl i.1))) 0 else ev2 n 0 i.1 (e₁ i.1) (B i.1) 0

private theorem prod_cv {S : Set (Pl E)} (T : Finset (Pl E)) (B : Pl E → Multiset ℂˣ)
    (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (hT : TEv S T e₂) :
    ∏ i ∈ (T ×ˢ Finset.univ).filter (Sl S), cv B e₁ e₂ i = val T e₁ e₂ B 0 := by
  rw [Finset.prod_filter, Finset.prod_product, val]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hS := hT.1 w hw
  rw [Fintype.prod_bool]
  by_cases hs : IsSplitAt w
  · have h1 : Sl S (w, true) := ⟨hS, fun _ => hs⟩
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    simp [h1, h2, cv, inv, mul_comm]
  · have h1 : ¬ Sl S (w, true) := fun h => hs (h.2 rfl)
    have h2 : Sl S (w, false) := ⟨hS, by simp⟩
    have h3 : ev2 n 0 w (e₂ w) (inv (B (cPl w))) (inv ((0 : Pl E → Multiset ℂˣ) (cPl w))) = 1 := hT.2 w hw hs _
    simp only [h1, h2, if_true, if_false, cv, one_mul]
    rw [h3, mul_one]
    simp

private theorem off_of (hPl : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places) {S : Set (Pl E)} {Z : Finset (Pl E)} (hS : IsSection S)
    (hZ : SplitIn S Z) {w : Pl E} (hw : w ∈ S) (hwZ : w ∉ Z) : Off Z w ∧ Off Z (cPl w) := by
  have hc : cPl w ∉ Z := fun h => by
    have := ((hPl E).2.2.2 S hS w).2 hw (hZ _ h).1
    exact hwZ (this ▸ h)
  exact ⟨⟨hwZ, hc⟩, hc, by rwa [((hPl E).2.1 w).1]⟩

theorem tTr_pf :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → PfHecke → ProdOp → LocComm → YLoc → Ex2Act → SatAll → TTr := by
  intro hPl hPf hPO hLC _ hEx hSat E _ _ _ n S Z N hS hZ hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hT
  have hF := fam_positions hEx hZ hG φ₁ φ₂ hφ T hTZ e₁ e₂
  have hF0 : Fam S N (Z ×ˢ Finset.univ) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂)) := by
    simpa [slots] using fam_positions (S := S) hEx hZ hG φ₁ φ₂ hφ ∅ (Finset.disjoint_empty_left _) e₁ e₂
  have hH := hPf E n S Z N hS hZ hG _ _ hF
  have hH0 := hPf E n S Z N hS hZ hG _ _ hF0
  refine ⟨hH, hF0, LinearMap.ext fun x => Subtype.ext ?_⟩
  have hxf := y.fix x.2
  rw [LinearMap.smul_apply, Submodule.coe_smul, y.act _ hH x, y.act _ hH0 x,
    hPO E n S Z N hS hZ hG _ _ hF _ hxf, hPO E n S Z N hS hZ hG _ _ hF0 _ hxf]
  set F := two (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) with hFdef
  set L : Pl E × Bool → Module.End ℂ (Sm E n) := fun i => Lw N i.1 i.2 (F i.1 i.2) with hL
  have hd : Disjoint (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ((T ×ˢ Finset.univ).filter (Sl S)) := by
    refine Finset.disjoint_left.2 fun i h1 h2 => ?_
    exact Finset.disjoint_left.1 hTZ (Finset.mem_product.1 (Finset.mem_filter.1 h2).1).1 (Finset.mem_product.1 h1).1
  have hcomm : ∀ i ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S),
      ∀ k ∈ (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S), i ≠ k → Commute (L i) (L k) := by
    intro i hi k hk hik
    exact (hLC E n S Z N hS hZ hG i (hF.1 i hi).1 _ (hF.1 i hi).2).2 k (hF.1 k hk).1 hik _ (hF.1 k hk).2
  have hsame : ((Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map fun i =>
      Lw N i.1 i.2 (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) i.1 i.2)) =
      (Z ×ˢ Finset.univ : Finset (Pl E × Bool)).toList.map L := by
    refine List.map_congr_left fun i hi => ?_
    have hw := (Finset.mem_product.1 (Finset.mem_toList.1 hi)).1
    simp only [hL, hFdef, two_in hw]
  have heig : ∀ i ∈ ((T ×ˢ Finset.univ).filter (Sl S)).toList, L i x.1 = cv B e₁ e₂ i • x.1 := by
    intro i hi
    obtain ⟨h1, hs⟩ := Finset.mem_filter.1 (Finset.mem_toList.1 hi)
    have hwT := (Finset.mem_product.1 h1).1
    have hwZ : i.1 ∉ Z := Finset.disjoint_left.1 hTZ hwT
    by_cases hx0 : x.1 = 0
    · simp [hx0]
    have hmem : i ∈ slots S Z T := Finset.mem_union_right _ (Finset.mem_filter.2 ⟨h1, hs⟩)
    have hfx := ((hLC E n S Z N hS hZ hG i hs _ (hF.1 i hmem).2).1 x.1 hxf).1
    rw [(hG i.1).2.2.2 hwZ] at hfx
    obtain ⟨ho, ho'⟩ := off_of hPl hS hZ hs.1 hwZ
    obtain ⟨w, b⟩ := i
    have hN : N w = KGL w (n := n) := (hG w).2.2.2 hwZ
    have hxV := y.le x.2
    cases b
    · have hv := (hSat E n π w (B w) x.1 hxV hx0).1 (hB w ho) hfx
      have := (hEx E n w (e₁ w)).2 _ _ x.1 (B w) hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).1, cv, Lw, hN]
      simpa using this
    · have hv := (hSat E n π w (B (cPl w)) x.1 hxV hx0).2 (by
        have := hB (cPl w) ho'
        exact this) hfx
      have := (hEx E n w (e₂ w)).2 _ _ x.1 _ hv
      simp only [hL, hFdef, (slot_pair_functions_eq hwZ hwT φ₁ φ₂ e₁ e₂).2, cv, Lw, hN]
      simpa using this
  have hI : slots S Z T = (Z ×ˢ Finset.univ : Finset (Pl E × Bool)) ∪ (T ×ˢ Finset.univ).filter (Sl S) := rfl
  rw [hsame, hI, prod_split L _ _ hd hcomm, Module.End.mul_apply, list_eig L (cv B e₁ e₂) x.1 _ heig,
    Finset.prod_map_toList, prod_cv T B e₁ e₂ hT, map_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open PositivityTheory.Rg.BcB.CG.prime_not_mem_section_base_place
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem uAt_mul' (v : InfinitePlace E) (k k' : Kinf E n) : uAt v (k * k') = uAt v k * uAt v k' := by
  apply Subtype.ext
  show ((k * k' : Kinf E n) : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) =
    (k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) * (k' : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)
  rw [← Matrix.map_mul]
  rfl

private theorem coef_mul' (M : Mods E n) (I L : IxA M) (x k : Kinf E n) :
    coef M I L (x * k) = ∑ m : IxA M, coef M I m k * coef M m L x := by
  have h1 : ∀ v, ent (M v) ((M v).ρ (uAt v (x * k)⁻¹)) (I v) (L v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) := by
    intro v
    rw [_root_.mul_inv_rev, uAt_mul', map_mul, PMul.ent_mul]
  calc coef M I L (x * k)
      = ∏ v, ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) :=
        Finset.prod_congr rfl fun v _ => h1 v
    _ = ∑ m ∈ Fintype.piFinset fun _ => Finset.univ,
          ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (m v) * ent (M v) ((M v).ρ (uAt v x⁻¹)) (m v) (L v) :=
        Finset.prod_univ_sum _ _
    _ = ∑ m : IxA M, coef M I m k * coef M m L x := by
        simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, coef]

private theorem rinv_Wsp (M : Mods E n) : RInv (Wsp M) := by
  intro f hf k
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨p, rfl⟩ := h
    have e : (fun x => coef M p.1 p.2 (x * k)) = ∑ m : IxA M, coef M p.1 m k • coef M m p.2 := by
      funext x
      simp only [coef_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun x => coef M p.1 p.2 (x * k)) ∈ Wsp M
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, p.2), rfl⟩)
  | zero => exact (Wsp M).zero_mem
  | add a b _ _ ha hb => exact (Wsp M).add_mem ha hb
  | smul c a _ ha => exact (Wsp M).smul_mem c ha

private theorem level_open_compact {b : ℕ} (U : Subgroup (Hf E n b)) (hU : IsOpen (U : Set (Hf E n b))) :
    IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) ∧
      IsCompact ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have h1 : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    hU.preimage (Continuous.prodMk_left 1)
  have h2 : IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    h1.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  exact ⟨h2, (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h2) Set.inter_subset_right⟩

end SlopeTestRemainingChoices

theorem tensType_pf : TensType := by
  intro E _ _ _ n μa μb _ _ Ma Mb κ ka kb va vb R ψ U ha hb hψ hU hlev i j
  obtain ⟨hKo, hKc⟩ := level_open_compact U hU
  refine ⟨tens_cs ha hb hψ i j, _, Wsp Ma, hKo, hKc, fd_Wsp Ma, rinv_Wsp Ma, fun u hu y => ?_, fun y => ?_⟩
  · have e1 : entA ka i.1.1 j.1.1 (finGL E n u * y.1) = entA ka i.1.1 j.1.1 y.1 := by
      have h := entA_fin ka i.1.1 j.1.1 u⁻¹ y.1
      rwa [map_inv, inv_inv] at h
    have e2 : hFin ((finGL E n u, 1) * y) = ((u, 1) : Hf E n 0) * hFin y := by
      show (gFin (finGL E n u * y.1), gFin (1 * y.2)) = (u * gFin y.1, 1 * gFin y.2)
      rw [map_mul, gFin_finGL, one_mul, one_mul]
    show entA ka i.1.1 j.1.1 (finGL E n u * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
        ψ i.2 j.2 (hFin ((finGL E n u, 1) * y)) = entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
    rw [e1, one_mul, e2, hlev i.2 j.2 (u, 1) hu.1 (hFin y)]
  · have e : (fun k : Kinf E n => tens ka kb ψ i j (((kI E n k)⁻¹, 1) * y)) =
        ∑ L : IxA Ma, (entA ka L j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)) • coef Ma i.1.1 L := by
      funext k
      have e2 : hFin (((kI E n k)⁻¹, 1) * y) = hFin y := by
        have h1 : gFin (infGL E n (Unitary.toUnits k)) = 1 := pFin_infGL _
        show (gFin ((infGL E n (Unitary.toUnits k))⁻¹ * y.1), gFin (1 * y.2)) = (gFin y.1, gFin y.2)
        rw [map_mul, map_inv, h1, inv_one, one_mul, one_mul]
      show entA ka i.1.1 j.1.1 ((infGL E n (Unitary.toUnits k))⁻¹ * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
          ψ i.2 j.2 (hFin (((kI E n k)⁻¹, 1) * y)) = _
      rw [entA_inf ha, one_mul, e2, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun L _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i.1.1, L), rfl⟩)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end
