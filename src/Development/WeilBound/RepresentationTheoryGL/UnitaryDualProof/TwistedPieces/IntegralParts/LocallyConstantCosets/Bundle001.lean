module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousLinearMat
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousOnZpart
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ZpartUnique
public import GroundTheory.AutomorphicForms.WhittakerDistribution
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.UnifLC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lc_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  intro s
  by_cases h1 : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · convert isOpen_univ using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isOpen using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isClosed.isOpen_compl using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert isOpen_empty using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]

theorem psi_lift (hZ : CR Z) {A : Set (Matrix (Fin n) (Fin n) k)} (hAZ : A ⊆ Z) (hAc : IsCompact A)
    (hAo : ∀ a ∈ A, ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ A)
    {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z A h p := by
  classical
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hUU : IsOpen (UU : Set (Sp k n)) := isOpen_ne_fun continuous_snd continuous_const
  have hOU : OO Z ⊆ UU := fun p hp => hp.2
  have hhl : IsLocallyConstant h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).1
  have hhc : HasCompactSupport h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).2

  have hg1 : Continuous (fun p : OO Z => zpart Z (p : Sp k n).1) :=
    (continuousOn_zpart hZ).comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hg2 : Continuous (fun p : OO Z => (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2) : Sp k n)) :=
    ((continuous_fst.comp continuous_subtype_val).sub hg1).prodMk (continuous_snd.comp continuous_subtype_val)

  set S : Set (OO Z) := {p | zpart Z (p : Sp k n).1 ∈ A} with hSdef
  have hSc : IsClosed S := hAc.isClosed.preimage hg1
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hU, hpU, hUA⟩ := hAo _ hp
    refine ⟨(fun q : OO Z => zpart Z (q : Sp k n).1) ⁻¹' U, fun q hq => hUA ⟨hq, (zpart_spec q.2.1).1⟩,
      hU.preimage hg1, hpU⟩
  have hphi : (fun p : OO Z => psi Z A h p) =
      fun p => S.indicator (fun _ => (1 : ℂ)) p * h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) := by
    funext p
    rw [psi_of_mem p.2.1]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show zpart Z (p : Sp k n).1 ∈ A from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show zpart Z (p : Sp k n).1 ∉ A from hp)]

  have hsupp_cl : IsClosed (Function.support h) := by
    have : Function.support h = (h ⁻¹' {0})ᶜ := by ext x; simp [Function.mem_support]
    rw [this]
    exact (hhl.isOpen_fiber 0).isClosed_compl
  have hts : tsupport h ⊆ UU := by
    rw [tsupport, hsupp_cl.closure_eq]; exact hh.2

  set K : Set (Matrix (Fin n) (Fin n) k × Sp k n) := A ×ˢ (tsupport h ∩ (NB Z ×ˢ Set.univ)) with hK
  have hKc : IsCompact K := hAc.prod (hhc.inter_right ((isClosed_NB Z).prod isClosed_univ))
  set Φ : Matrix (Fin n) (Fin n) k × Sp k n → Sp k n := fun aq => (aq.1 + aq.2.1, aq.2.2) with hΦ
  have hΦc : Continuous Φ := (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)
  have hΦO : Φ '' K ⊆ OO Z := by
    rintro _ ⟨⟨a, q⟩, ⟨ha, hq, hqN⟩, rfl⟩
    have h2 : q.2 ≠ 0 := hts hq
    exact ⟨(cc_of_NB hZ (hAZ ha) hqN.1).1, h2⟩
  set Kc : Set (OO Z) := (Subtype.val : OO Z → Sp k n) ⁻¹' (Φ '' K) with hKcdef
  have hKcc : IsCompact Kc := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hΦO]
    exact hKc.image hΦc
  have hsub : Function.support (fun p : OO Z => psi Z A h p) ⊆ Kc := by
    intro p hp
    rw [hphi, Function.mem_support] at hp
    have hpS : p ∈ S := by
      by_contra hn; rw [Set.indicator_of_notMem hn, zero_mul] at hp; exact hp rfl
    have hq : h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) ≠ 0 := by
      rw [Set.indicator_of_mem hpS, one_mul] at hp; exact hp
    refine ⟨(zpart Z (p : Sp k n).1, (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2))),
      ⟨hpS, subset_tsupport _ hq, sub_mem_NB hZ p.2.1, Set.mem_univ _⟩, ?_⟩
    simp only [hΦ, add_sub_cancel]
  obtain ⟨f, hf, hfe⟩ := GroundTheory.Automorphic.Whittaker.exists_lift hUU hOU (φ := fun p : OO Z => psi Z A h p) (by
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport]
    refine ⟨?_, ?_⟩
    · rw [hphi]
      exact IsLocallyConstant.comp₂ (lc_indicator ⟨hSc, hSo⟩ 1) (hhl.comp_continuous hg2) (· * ·)
    · exact IsCompact.of_isClosed_subset hKcc isClosed_closure (closure_minimal hsub hKcc.isClosed))
  exact ⟨f, hf, fun p hp => hfe ⟨p, hp⟩⟩

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem psi_cosets {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) :
    ∃ D : Finset (Matrix (Fin n) (Fin n) k), D.card = M.relIndex L ∧ (∀ d ∈ D, d ∈ L) ∧
      ∀ h : Sp k n → ℂ, psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h =
        ∑ d ∈ D, psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨lat_index_pos hL hM hML⟩
  haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  let f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k := fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)
  have hf : Function.Injective f := fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)
  have hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M := by
    intro z q
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - f q, hz, by simp⟩
  have key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
      ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z := by
    intro z
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      have hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator
          (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
          if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0 := by
        intro q
        have e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) =
            QuotientAddGroup.mk (Quotient.out q) := by
          rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          show z - f q ∈ M ↔ -z + f q ∈ M
          rw [show -z + f q = -(z - f q) by abel, neg_mem_iff]
        rw [QuotientAddGroup.out_eq'] at e
        by_cases h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q
        · rw [if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]
      simp only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro h'
      apply hz
      have h2 : z = (z - f q) + f q := by abel
      rw [h2]
      exact L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2
  refine ⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hd
    exact (Quotient.out q).2
  · rw [Finset.sum_apply]
    by_cases hp : p.1 ∈ CC Z
    · simp only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]
      rw [key, Finset.sum_mul]
    · simp only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem dec (hZ : CR Z) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) {t : kˣ}
    (ht : nabs k t < 1) {F : Sp k n → ℂ} (hF : F ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ (j : ℕ) (S : Finset (Matrix (Fin n) (Fin n) k)), (∀ c ∈ S, c ∈ Z) ∧
      ∀ p ∈ OO Z, F p = ∑ c ∈ S, psi Z ((fun a => a + c) '' ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set _))
        (fun q => F (tr c q)) p := by
  classical
  obtain ⟨W, hW, hWF⟩ := unifLC hF.1
  obtain ⟨j, hj⟩ := lat_small hL ht hW
  have hLat' : IsLat Z ((((t ^ j : kˣ) : k) • L : AddSubgroup (Matrix (Fin n) (Fin n) k))) := isLat_smul hL (t ^ j)
  set L' : AddSubgroup (Matrix (Fin n) (Fin n) k) := (((t ^ j : kˣ) : k) • L) with hLe
  have hL'W : ∀ w ∈ L', w ∈ W := fun w hw => hj (by rw [← AddSubgroup.coe_pointwise_smul]; exact hw)
  obtain ⟨U, hUo, hU0, hUZ⟩ := hLat'.nhd
  have hK : IsCompact (Prod.fst '' tsupport F) := hF.1.2.image continuous_fst
  obtain ⟨S0, hS0, hS0Z, hS0K⟩ := exists_cpt hZ hK
  obtain ⟨S1, hS1⟩ := hS0.elim_finite_subcover (fun c : S0 => (fun a => a + (c : Matrix (Fin n) (Fin n) k)) '' U)
    (fun c => isOpenMap_add_right _ U hUo) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, 0, hU0, zero_add s⟩)
  let g : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k :=
    fun c => Quotient.out (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L')
  have hg : ∀ c, g c - c ∈ L' := by
    intro c
    have h1 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L'))
    have h2 : g c - c = -(-(g c) + c) := by abel
    rw [h2]
    exact L'.neg_mem h1
  have hgeq : ∀ c c', c - c' ∈ L' → g c = g c' := by
    intro c c' h
    show Quotient.out _ = Quotient.out _
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    rw [show -c + c' = -(c - c') by abel]
    exact L'.neg_mem h
  have hgg : ∀ a a', g a - g a' ∈ L' → g a = g a' := by
    intro a a' h
    apply hgeq
    have e : a - a' = (g a - g a') - (g a - a) + (g a' - a') := by abel
    rw [e]
    exact L'.add_mem (L'.sub_mem h (hg a)) (hg a')
  have hmemI : ∀ z c, z ∈ (fun a => a + c) '' (L' : Set (Matrix (Fin n) (Fin n) k)) ↔ z - c ∈ L' := by
    intro z c
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - c, hz, by simp⟩
  refine ⟨j, S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    have e : g (i : Matrix (Fin n) (Fin n) k) = (i : Matrix (Fin n) (Fin n) k) + (g i - i) := by abel
    rw [e]
    exact Z.add_mem (hS0Z i.2) (hLat'.sub (hg _))
  · rintro ⟨x, v⟩ hp
    have hx : x ∈ CC Z := hp.1
    simp only [psi_of_mem (p := (x, v)) hx, tr]
    by_cases hA : ∃ c ∈ S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), zpart Z x - c ∈ L'
    · obtain ⟨c, hcS, hcz⟩ := hA
      rw [Finset.sum_eq_single c]
      · rw [Set.indicator_of_mem ((hmemI _ _).2 hcz), Pi.one_apply, one_mul]
        have e : x - zpart Z x + c = x + (c - zpart Z x) := by abel
        rw [e]
        have hw : c - zpart Z x ∈ L' := by
          rw [show c - zpart Z x = -(zpart Z x - c) by abel]
          exact L'.neg_mem hcz
        exact (hWF _ (hL'W _ hw) (x, v)).symm
      · intro c' hc' hne
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        apply hne
        obtain ⟨a', _, rfl⟩ := Finset.mem_image.1 hc'
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hcS
        apply hgg
        have e : g (a' : Matrix (Fin n) (Fin n) k) - g a = (zpart Z x - g a) - (zpart Z x - g a') := by abel
        rw [e]
        exact L'.sub_mem hcz ((hmemI _ _).1 h')
      · intro h
        exact absurd hcS h
    · push_neg at hA
      rw [Finset.sum_eq_zero]
      · by_contra hne
        have hsupp : (x, v) ∈ tsupport F := subset_tsupport F hne
        have hz := hS0K x ⟨⟨(x, v), hsupp, rfl⟩, hx⟩
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hS1 hz)
        obtain ⟨u, hu, hue⟩ := hzi
        simp only at hue
        have huZ : u ∈ Z := by
          have e : u = zpart Z x - i := by rw [← hue]; abel
          rw [e]
          exact Z.sub_mem (hS0Z hz) (hS0Z i.2)
        have huL : u ∈ L' := hUZ ⟨hu, huZ⟩
        apply hA (g i) (Finset.mem_image.2 ⟨i, hi, rfl⟩)
        have e : zpart Z x - g i = u - (g i - i) := by rw [← hue]; abel
        rw [e]
        exact L'.sub_mem huL (hg _)
      · intro c hc
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        exact hA c hc ((hmemI _ _).1 h')

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end
