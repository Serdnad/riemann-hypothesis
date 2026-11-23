module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Mathlib.RingTheory.AdjoinRoot
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_surj_over_finite :
    ∀ (P Γ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] [Group Γ] (r h : ℕ) (x : Fin (r + h) → P) (γ : Fin r → Γ) (π : P →* Γ), TopGen (Set.range x) →
      (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin (r + h) → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i) →
      Function.Surjective γ → IsOpen (π.ker : Set P) → (∀ i, π (x (Fin.castAdd h i)) = γ i) → (∀ i, π (x (Fin.natAdd r i)) = 1) →
      ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (q : G →* Γ), IsOpen (q.ker : Set G) → ∀ g : Fin r → G, (∀ i, q (g i) = γ i) →
        (∃ z : Fin h → q.ker, TopGen (Set.range z)) →
        ∃ f : P →* G, Continuous f ∧ Function.Surjective f ∧ q.comp f = π ∧ ∀ i, f (x (Fin.castAdd h i)) = g i := by
  intro P Γ _ _ _ _ _ _ r h x γ π hden huniv hγ hπo hπl hπr G _ _ _ _ _ q hqo g hg hz
  obtain ⟨z, hzd⟩ := hz
  obtain ⟨f, hf, hfx⟩ := huniv G (Fin.append g (fun j => (z j : G)))
  have hfl : ∀ i, f (x (Fin.castAdd h i)) = g i := fun i => by
    rw [hfx, Fin.append_left]
  have hfr : ∀ j, f (x (Fin.natAdd r j)) = z j := fun j => by
    rw [hfx, Fin.append_right]
  refine ⟨f, hf, ?_, ?_, hfl⟩
  · haveI : T2Space G := inferInstance
    have hRc : IsClosed (Set.range f) := (isCompact_range hf).isClosed
    have hker : ∀ k : q.ker, (k : G) ∈ Set.range f := by
      let S : Set q.ker := Subtype.val ⁻¹' Set.range f
      have hSc : IsClosed S := hRc.preimage continuous_subtype_val
      have hsub : ((Subgroup.closure (Set.range z) : Subgroup q.ker) : Set q.ker) ⊆ S := by
        have : Subgroup.closure (Set.range z) ≤ f.range.comap q.ker.subtype := by
          rw [Subgroup.closure_le]
          rintro _ ⟨j, rfl⟩
          exact ⟨x (Fin.natAdd r j), hfr j⟩
        intro a ha
        exact this ha
      have hdS : Dense S := hzd.mono hsub
      intro k
      have : k ∈ S := by
        rw [← hSc.closure_eq, hdS.closure_eq]
        trivial
      exact this
    intro a
    obtain ⟨i, hi⟩ := hγ (q a)
    have hmem : (g i)⁻¹ * a ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg i, hi, inv_mul_cancel]
    obtain ⟨p1, hp1⟩ := hker ⟨_, hmem⟩
    refine ⟨x (Fin.castAdd h i) * p1, ?_⟩
    rw [map_mul, hfl, hp1]
    simp
  · set φ := q.comp f with hφ
    have hgen : Set.EqOn φ π (Set.range x) := by
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hφ, hfl, hg, hπl]
      | right j =>
        simp only [hφ, MonoidHom.comp_apply, hfr, hπr]
        exact (z j).2
    have hcl : Set.EqOn φ π (Subgroup.closure (Set.range x)) := MonoidHom.eqOn_closure hgen
    have hφo : IsOpen (φ.ker : Set P) := by
      have : (φ.ker : Set P) = f ⁻¹' (q.ker : Set G) := by
        ext a
        simp [hφ]
      rw [this]
      exact hqo.preimage hf
    ext p
    let V : Set P := (fun a => p⁻¹ * a) ⁻¹' ((π.ker : Set P) ∩ (φ.ker : Set P))
    have hVo : IsOpen V := (hπo.inter hφo).preimage (continuous_const.mul continuous_id)
    have hpV : p ∈ V := by
      simp [V]
    obtain ⟨d, ⟨hd1, hd2⟩, hdD⟩ := hden.inter_open_nonempty V hVo ⟨p, hpV⟩
    have e1 : π (p⁻¹ * d) = 1 := hd1
    have e2 : φ (p⁻¹ * d) = 1 := hd2
    rw [map_mul, map_inv, inv_mul_eq_one] at e1 e2
    rw [e2, hcl hdD, ← e1]
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff {l : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

theorem UpperTheory.V.AlgebraTools.proLRes_map :
    ∀ (l : ℕ) [Fact l.Prime] (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (f : G →* H), Continuous f → Function.Surjective f →
      (proLRes l G).map f = proLRes l H := by
  intro l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, mem_proLRes]
    intro N hN
    rw [pq_iff] at hN
    let M : OpenNormalSubgroup G :=
      { toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup
        isNormal' := Subgroup.Normal.comap inferInstance f }
    haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'
    have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro x
      obtain ⟨k, hk⟩ := hN (f x)
      refine ⟨k, ?_⟩
      show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup
      rw [OpenSubgroup.mem_comap, map_pow]
      exact hk
    have := (mem_proLRes.mp hg) M hM
    exact (OpenSubgroup.mem_comap (hf := hf)).mp this
  · intro h hh
    rw [mem_proLRes] at hh
    let t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G :=
      fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)
    let T0 : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }
    haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'
    have htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro g
      refine ⟨0, ?_⟩
      show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)
      simp
    haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩
    have hcl : ∀ i, IsClosed (t i) := fun i =>
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
      intro i j
      have hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G)) := by
        rw [pq_iff]
        intro g
        obtain ⟨a, ha⟩ := (pq_iff _).mp i.2 g
        obtain ⟨b, hb⟩ := (pq_iff _).mp j.2 g
        refine ⟨a + b, ?_⟩
        have e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b := by rw [pow_add, pow_mul]
        have e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a := by rw [add_comm, pow_add, pow_mul]
        have m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G) := e1 ▸ pow_mem ha _
        have m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G) := e2 ▸ pow_mem hb _
        show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)
        exact OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩
      refine ⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩
    have hnon : ∀ i, (t i).Nonempty := by
      intro i
      have hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G) := i.1.toOpenSubgroup.isClosed
      have hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H) := by
        rw [Subgroup.coe_map]
        exact hf.isClosedMap _ hNcl
      haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by
        rw [Subgroup.finiteIndex_iff]
        intro h0
        have hd := Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs
        rw [h0, zero_dvd_iff] at hd
        exact (Subgroup.finiteIndex_iff.mp inferInstance) hd
      let M : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f,
            Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩
          isNormal' := Subgroup.Normal.map inferInstance f hs }
      haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'
      have hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H)) := by
        rw [pq_iff]
        intro y
        obtain ⟨x, rfl⟩ := hs y
        obtain ⟨k, hk⟩ := (pq_iff _).mp i.2 x
        refine ⟨k, ?_⟩
        show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f
        exact ⟨x ^ l ^ k, hk, map_pow f x _⟩
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp (hh M hM)
      exact ⟨x, hfx, hx⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
      (fun i => (hcl i).isCompact) hcl
    rw [Set.mem_iInter] at hg
    refine ⟨g, ?_, (hg (Classical.arbitrary _)).1⟩
    rw [SetLike.mem_coe, mem_proLRes]
    intro N hN
    exact (hg ⟨N, hN⟩).2
end

section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → ∀ n : ℕ, (p ^ n).map (algebraMap R B) = maximalIdeal B ^ n := by
  intro R _ p B _ _ _ h n
  have hnoeth := h.noeth
  have hle : p.map (algebraMap R B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  have heq : p.map (algebraMap R B) = maximalIdeal B := by
    refine le_antisymm hle ?_
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
    intro b hb
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 b
    have hsu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self two_ne_zero
    have ha : a ∈ p := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have : algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)
    obtain ⟨u, hu⟩ := hsu
    have hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a)) := by
      rw [← hu]
      simp
    rw [hb', smul_eq_mul, ← pow_two]
    apply Ideal.mul_mem_left
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)
  rw [Ideal.map_pow, heq]
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.tnAlg_smul_mem {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R) (a : A) {y : M}
    (hy : y ∈ (I • ⊤ : Submodule R M)) : a • y ∈ (I • ⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro u v hu hv
    rw [smul_add]
    exact Submodule.add_mem _ hu hv

private theorem UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R)
    {a : A} (ha : a ∈ I.map (algebraMap R A)) (y : M) : a • y ∈ (I • ⊤ : Submodule R M) := by
  unfold Ideal.map at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_smul]; exact Submodule.add_mem _ hb hc
  | smul b c _ hc =>
    rw [smul_eq_mul, mul_smul]
    exact UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc

private theorem UpperTheory.V.AlgebraTools.tnAlg_mem_radical {R A : Type} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] {a : A}
    (ha : ∀ n : Ideal A, n.IsMaximal → a ∈ n) :
    a ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).radical := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  apply ha
  have hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P := by
    intro r hr
    rw [Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ hr)
  have hne : Ideal.comap (algebraMap R A) P ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
  have hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R :=
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm
  have hcm : (Ideal.comap (algebraMap R A) P).IsMaximal := by
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P hcm

theorem UpperTheory.V.AlgebraTools.topNil_eq_idem :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A κ : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (t : κ → A),
      ∃ e : A, IsIdempotentElem e ∧ (∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)) ∧
        ∀ (M : Type) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite R M] (x : M),
          x ∈ topNil (IsLocalRing.maximalIdeal R) (fun i => (Algebra.lsmul R R M (t i) : Module.End R M)) ↔ e • x = x := by
  intro R _ _ _ _ A κ _ _ _ t
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨e, he, hT⟩ := GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A)
    {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}
  have hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n) := fun n hn => hT ⟨n, hn⟩
  refine ⟨e, he, hmax, ?_⟩
  intro M _ _ _ _ _ x
  have hpow : ∀ (a : A) (r : ℕ) (y : M),
      ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y := by
    intro a r y
    rw [← map_pow, Algebra.lsmul_coe]
  rw [mem_topNil_iff_exists]
  simp only [hpow]
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M) :=
    fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy
  constructor
  · intro hx
    set y := x - e • x with hy
    have hey : e • y = 0 := by rw [hy, smul_sub, smul_smul, he.eq, sub_self]
    suffices y = 0 by rw [sub_eq_zero] at this; exact this.symm
    have hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M) := by
      intro j
      let P : Submodule A M :=
        { carrier := (m ^ j • ⊤ : Submodule R M)
          add_mem' := fun ha hb => Submodule.add_mem _ ha hb
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun a _ hb => hA j a _ hb }
      let K : Ideal A := P.comap (LinearMap.toSpanSingleton A M y)
      have hKe : e ∈ K := by
        show e • y ∈ P
        rw [hey]
        exact P.zero_mem
      have hKt : ∀ i, t i ∈ K.radical := by
        intro i
        obtain ⟨r, hr⟩ := hx i j
        refine ⟨r, ?_⟩
        show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)
        rw [hy, smul_sub]
        refine Submodule.sub_mem _ hr ?_
        rw [smul_comm (t i ^ r) e x]
        exact hA j e _ hr
      have htop : K.radical = ⊤ := by
        by_contra hne
        obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
        exact ((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))
      have h1 : (1 : A) ∈ K.radical := htop ▸ Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      have h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M) := hr
      rw [one_pow, one_smul] at h2
      exact h2
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m
      (by rw [hm, IsLocalRing.ringJacobson_eq_maximalIdeal])
    have hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at hyi
    exact hyi
  · intro hx i j
    have hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n := by
      intro n hn
      by_cases h : e ∈ n
      · exact n.mul_mem_left _ h
      · exact n.mul_mem_right _ ((hmax n hn).mp h i)
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin
    refine ⟨N * j, ?_⟩
    have hex : ∀ k : ℕ, e ^ k • x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hx, ih]
    have hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A) := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_mem_pow hN j
    have h3 := UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x
    rwa [mul_pow, mul_smul, hex] at h3
end

section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.splitAlg_succ_equiv :
    ∀ (R : Type) [CommRing R] (n : ℕ) (P : Polynomial R), P.Monic → P.natDegree = n + 1 →
      ∃ (_ : Algebra (AdjoinRoot P) (SplitAlg P (n + 1))) (_ : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1))),
        algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 ∧
        ∃ e : SplitAlg P (n + 1) ≃ₐ[AdjoinRoot P]
            SplitAlg ((P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P))) n,
          ∀ i : Fin n, e (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root _ n i := by
  intro R _ n P hP hdeg
  have hroot0 : Polynomial.eval₂ (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) P = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, ← SplitAlg.prod_root, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  let φ : AdjoinRoot P →+* SplitAlg P (n + 1) :=
    AdjoinRoot.lift (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) hroot0
  letI alg : Algebra (AdjoinRoot P) (SplitAlg P (n + 1)) := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (algebraMap R (AdjoinRoot P) r)
      = algebraMap R (SplitAlg P (n + 1)) r := fun r => AdjoinRoot.lift_of hroot0
  haveI tower : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  have hr0 : algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 :=
    AdjoinRoot.lift_root hroot0
  refine ⟨alg, tower, hr0, ?_⟩
  set Q := (P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) with hQ
  have hfac : P.map (algebraMap R (AdjoinRoot P)) = (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) * Q := by
    rw [hQ, eq_comm, Polynomial.mul_divByMonic_eq_iff_isRoot, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.isRoot_root P
  have hmapS : P.map (algebraMap R (SplitAlg P (n + 1)))
      = (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) 0))
        * Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    rw [IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg P (n + 1)), ← Polynomial.map_map, hfac,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hr0]
  have hg : ∏ i : Fin n, (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) i.succ))
      = Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    have h1 := SplitAlg.prod_root P (n + 1)
    rw [Fin.prod_univ_succ, hmapS] at h1
    exact (Polynomial.monic_X_sub_C _).isRegular.left h1
  let g : SplitAlg Q n →ₐ[AdjoinRoot P] SplitAlg P (n + 1) :=
    SplitAlg.lift Q n (fun i => SplitAlg.root P (n + 1) i.succ) hg
  let a : Fin (n + 1) → SplitAlg Q n :=
    Fin.cons (algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P)) (SplitAlg.root Q n)
  have hf : ∏ i, (Polynomial.X - Polynomial.C (a i)) = P.map (algebraMap R (SplitAlg Q n)) := by
    rw [Fin.prod_univ_succ]
    simp only [a, Fin.cons_zero, Fin.cons_succ]
    rw [SplitAlg.prod_root, IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg Q n), ← Polynomial.map_map,
      hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  let f : SplitAlg P (n + 1) →ₐ[R] SplitAlg Q n := SplitAlg.lift P (n + 1) a hf
  have hf0 : f (SplitAlg.root P (n + 1) 0) = algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P) := by
    simp only [f, SplitAlg.lift_root, a, Fin.cons_zero]
  have hfs : ∀ i : Fin n, f (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root Q n i := by
    intro i
    simp only [f, SplitAlg.lift_root, a, Fin.cons_succ]
  have hfK : f.comp (IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg P (n + 1)))
      = IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg Q n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom', hr0, hf0]
  let fK : SplitAlg P (n + 1) →ₐ[AdjoinRoot P] SplitAlg Q n :=
    { f with commutes' := fun k => DFunLike.congr_fun hfK k }
  have hgs : ∀ i : Fin n, g (SplitAlg.root Q n i) = SplitAlg.root P (n + 1) i.succ := by
    intro i
    exact SplitAlg.lift_root Q n _ hg i
  refine ⟨AlgEquiv.ofAlgHom fK g ?_ ?_, ?_⟩
  · apply SplitAlg.hom_ext
    intro i
    show f (g (SplitAlg.root Q n i)) = SplitAlg.root Q n i
    rw [hgs, hfs]
  · apply AlgHom.restrictScalars_injective R
    apply SplitAlg.hom_ext
    intro i
    show g (f (SplitAlg.root P (n + 1) i)) = SplitAlg.root P (n + 1) i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hf0, AlgHom.commutes, hr0]
    · rw [hfs, hgs]
  · intro i
    exact hfs i
end
