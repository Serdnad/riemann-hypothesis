module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LamEqOfKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  have : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    simp
  rw [GDet.lam, GDet.lam, this]

private theorem lam_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G) (f : A →+* A')
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 i
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at this

private theorem coeff_cong {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (I : Ideal A)
    (x y : MonoidAlgebra A G) (h : ∀ i, D.lam i x - D.lam i y ∈ I) (k : ℕ) :
    (D.chi x).coeff k - (D.chi y).coeff k ∈ I := by
  by_cases hk : k ≤ n
  · have h1 := I.mul_mem_left ((-1) ^ (n - k)) (h (n - k))
    rw [GDet.lam, GDet.lam, Nat.sub_sub_self hk, ← mul_sub, ← mul_assoc, ← mul_pow] at h1
    simpa using h1
  · have hd : ∀ z, (D.chi z).coeff k = 0 := fun z => by
      rw [← (UpperTheory.V.CA.d_toDet D z).1]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (UpperTheory.V.CA.d_chi D.toDet z).2.2.2.2.2.1 (not_le.1 hk))
    rw [hd, hd, sub_self]
    exact I.zero_mem

private theorem sees_glob {l : ℕ} [Fact l.Prime] {L : Loc} (G0 : Glob l L) {n : ℕ} {R : Type} [CommRing R]
    (D : GDet n R G0.G₀) (I : Ideal R) (hD : D.IsCont I) (e : ℕ) :
    ∃ V : OpenNormalSubgroup G0.Γ, ∀ g g' : G0.G₀, (g : G0.Γ) * (g' : G0.Γ)⁻¹ ∈ V → ∀ i,
      D.lam i (MonoidAlgebra.single g' 1) - D.lam i (MonoidAlgebra.single g 1) ∈ I ^ e := by
  obtain ⟨V0, hV0⟩ := UpperTheory.V.Pa.Core.dSees n R G0.G₀ D I hD e
  have hop : IsOpen (Subtype.val '' (V0 : Set G0.G₀) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ V0.isOpen
  obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hop ⟨1, one_mem V0, rfl⟩
  refine ⟨V, fun g g' hg i => hV0 i _ _ ?_⟩
  obtain ⟨a, ha, e⟩ := hV hg
  have e' : a = g * g'⁻¹ := Subtype.ext e
  have h2 : QuotientGroup.mk' V0.toSubgroup g' = QuotientGroup.mk' V0.toSubgroup g := by
    have : QuotientGroup.mk' V0.toSubgroup a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    rw [e', map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, h2]

private theorem sp_le {R : Type} [CommRing R] (I : Ideal R) {q n : ℕ} (P P' : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) (h : ∀ j k, (P j).coeff k - (P' j).coeff k ∈ I) :
    spIdeal P' ut ≤ spIdeal P ut ⊔ I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) := by
  unfold spIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, k, rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Ideal.subset_span ⟨j, k, rfl⟩, _, Ideal.mem_map_of_mem _ (h j k), ?_⟩
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, map_sub]
  ring

private theorem sp_lift (O : Type) [CommRing O] {R : Type} [CommRing R] [Algebra O R] {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) (K : Ideal (MvPowerSeries (Fin q × Fin n) R))
    (h : spIdeal P ut ≤ K) :
    ∃ f : Sp P ut →ₐ[O] (MvPowerSeries (Fin q × Fin n) R ⧸ K), (∀ z, f (Sp.mk P ut z) = Ideal.Quotient.mk K z) ∧
      ∀ b, f (algebraMap R _ b) = Ideal.Quotient.mk K (MvPowerSeries.C b) :=
  ⟨Ideal.Quotient.factorₐ O h, fun _ => rfl, fun _ => rfl⟩

theorem UpperTheory.V.Pa.Core.piCong :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), T.ProL → Adapted T (r := r) → ∀ e : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), (∀ j k, ((fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) j).coeff k - ((fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) j).coeff k ∈ maximalIdeal B ^ e) ∧ ∀ (a : W.R) (z z' : MvPowerSeries (Fin T.q × Fin n) B), m.π a = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) z → (A.m N).θ (m.ρ N a) = Sp.mk (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) z' → z - z' ∈ spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔ (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT hA e
  obtain ⟨V, hV⟩ := sees_glob G0 u.D (maximalIdeal B) u.cont e
  have h1 : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ j, (T.h N).p (T.ph N j) * (T.sg j : G0.Γ)⁻¹ ∈ V :=
    Filter.eventually_all.2 fun j => (T.ph_lim V j (by rw [hT.1]; exact bot_le)).filter_mono Λ.U_le
  filter_upwards [h1, Λ.p_lim V] with N h1 h2
  have hc := fun j => coeff_cong u.D _ _ _ (hV ((T.h N).p₀ (T.ph N j)) (T.sg j) (h1 j))
  refine ⟨hc, fun a z z' hz hz' => ?_⟩
  have hle := sp_le (maximalIdeal B ^ e) (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1))
    (fun j => u.D.chi (MonoidAlgebra.single ((T.h N).p₀ (T.ph N j)) 1)) (fun j i => algebraMap O B (A.ut j i)) hc
  set K := spIdeal (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) ⊔
    (maximalIdeal B ^ e).map (MvPowerSeries.C : B →+* MvPowerSeries (Fin T.q × Fin n) B) with hK
  by_cases hKt : K = ⊤
  · rw [hKt]; exact Submodule.mem_top
  haveI := Ideal.Quotient.nontrivial_iff.2 hKt
  obtain ⟨f, hf, hfb⟩ := sp_lift O _ _ K le_sup_left
  obtain ⟨f', hf', hfb'⟩ := sp_lift O _ _ K hle
  haveI := (spoCo l L G0 T Λ n O r B u J D A hA).1.1
  haveI : IsCO O (MvPowerSeries (Fin T.q × Fin n) B ⧸ K) := co_quot O (Spo A) _ f fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, hf y⟩
  obtain ⟨p1, p2, p3, p4, p5⟩ := m.π_maps
  obtain ⟨r1, r2, r3, r4, r5⟩ := m.ρ_maps N
  obtain ⟨t1, t2⟩ := (A.m N).θ_pair
  have key : f.comp m.π = f'.comp ((A.m N).θ.comp (m.ρ N)) := by
    refine rrExt l L G0 T Λ n O r B u J D A W _ _ _ (fun i g => ?_) (fun v i g => ?_) ?_ (fun j i => ?_) fun j i => ?_
    · have a1 := lam_map W.t.D m.π.toRingHom i g
      rw [p1, lam_map, lam_comap] at a1
      have a2 := lam_map W.t.D (m.ρ N).toRingHom i g
      rw [r1, lam_comap] at a2
      have a3 := lam_map (A.A N).p.D (A.m N).θ.toRingHom i (πN0 Λ N g)
      rw [t1, lam_map, lam_comap, a2] at a3
      refine (congrArg f a1.symm).trans (Eq.trans ?_ (congrArg f' a3))
      rw [hfb, hfb', Ideal.Quotient.eq, ← map_sub]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (hV _ _ (h2 g) i))
    · have a1 : m.π (W.t.ψ v i g) = algebraMap B _ (u.ψ v i g) := congrArg (fun χ => ((χ g : _ˣ) : Spo A)) (p2 v i)
      have a2 : m.ρ N (W.t.ψ v i g) = (A.A N).p.ψ v i g := congrArg (fun χ => ((χ g : _ˣ) : (A.A N).R)) (r2 v i)
      have a3 : (A.m N).θ ((A.A N).p.ψ v i g) = algebraMap B _ (u.ψ v i g) :=
        congrArg (fun χ => Units.val (χ g)) (t2 v i)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, a3, hfb, hfb']
    · rw [← m.s_X_unit, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
    · have a1 : m.π (W.t.U j i) = _ := p4 j i
      have a2 : m.ρ N (W.t.U j i) = _ := r4 j i
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, a1, a2, (A.m N).θ_U]
      exact (hf _).trans (hf' _).symm
    · rw [← m.s_y, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, m.π_s, m.specializationMap_comp_universalSection, (A.m N).theta_coefficientMap_eq, hfb, hfb']
  have k2 : f (m.π a) = f' ((A.m N).θ (m.ρ N a)) := DFunLike.congr_fun key a
  rw [hz, hz', hf, hf'] at k2
  exact Ideal.Quotient.eq.1 k2
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrGen :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), GenBy O ({b | ∃ i g, b = W.t.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((W.t.ψ v i g : W.Rˣ) : W.R)} ∪ {b | ∃ j i, b = W.t.U j i ∨ b = W.t.y j i} ∪ {W.t.s}) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W N x
  refine UpperTheory.V.CA.u_gen O W.R _ (fun R' _ _ _ f f' h => ?_) N x
  refine UpperTheory.V.Pa.Core.rrExt l L G0 T Λ n O r B u J D A W R' f f' (fun i g => h _ ?_) (fun v i g => h _ ?_)
    (h _ ?_) (fun j i => h _ ?_) (fun j i => h _ ?_)
  · exact .inl (.inl (.inl ⟨i, g, rfl⟩))
  · exact .inl (.inl (.inr ⟨v, i, g, rfl⟩))
  · exact .inr rfl
  · exact .inl (.inr ⟨j, i, .inl rfl⟩)
  · exact .inl (.inr ⟨j, i, .inr rfl⟩)
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_push {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : E.map f = D.comap φ) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

theorem UpperTheory.V.Pa.Core.eventually_trace_inertia_congruence_of_adapted :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (w : L.St) (g : L.Gu w) (ga h : Ph0 Λ), g ∈ L.Ju w → πo0 Λ ga = Λ.G.φu w g → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m had w g ga h hg hga j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φu_lim V] with N hk hφ
  obtain ⟨g', hg', hgv⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ga : Λ.Ph) (hφ w g)
    (congrArg Subtype.val hga)
  have hm : g' ∈ Ph0 Λ := by
    simpa using mul_mem ga.2 (hV0 hgv)
  let gN : Ph0 Λ := ⟨g', hm⟩
  have e0 : πN0 Λ N gN = (T.GN N).φu w g := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1)), hV 1 _ _ ?_, Or.inl ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ga =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) gN := QuotientGroup.eq.2 hgv
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, e]
  · have e1 : πN0 Λ N gN ∈ (A.A N).rN.Ip w := by
      rw [e0]
      refine ⟨⟨g, hg, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have h1 : G0.φu w g ∈ r.Ip w := by
        rw [had.2]
        exact ⟨g, hg, rfl⟩
      rw [MonoidHom.mem_ker, (A.A N).compat.1 i, MonoidHom.comp_apply, (T.h N).p₀_φu]
      exact Subgroup.mem_iInf.1 h1.2 i
    have hl := lam_push (m.ρ_maps N).1 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1))
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single] at hl
    exact hl.trans ((A.A N).p.I w _ e1 _)
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_dom {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (D : GDet n S G) (φ : H →* G)
    (i : ℕ) (z : MonoidAlgebra S H) : (D.comap φ).lam i z = D.lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  unfold GDet.lam
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

private theorem mapDomain_single_mul_charpoly_element {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (φ : H →* G) (h g : H)
    (U : Fin n → S) : MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single (φ h) 1 * q1El (φ g) U := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext i
    rw [Function.comp_apply, map_sub]
    simp

private theorem mapRingHom_single_mul_charpoly_element {n : ℕ} {R S H : Type} [CommRing R] [CommRing S] [Group H] (f : R →+* S) (h g : H)
    (U : Fin n → R) : MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single h 1 * q1El g fun i => f (U i) := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]
  congr 3
  funext i
  simp

theorem UpperTheory.V.Pa.Core.t3Q1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (ph h : Ph0 Λ), πo0 Λ ph = Λ.ph a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q1El ph (W.t.U a)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a ph h hph j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V] with N hk hc
  obtain ⟨g', hg', hgV⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ph : Λ.Ph) (hc a)
    (congrArg Subtype.val hph)
  have hmem : g' ∈ Ph0 Λ := by
    have := mul_mem ph.2 (hV0 hgV)
    rwa [mul_inv_cancel_left] at this
  let p' : Ph0 Λ := ⟨g', hmem⟩
  have hp' : πN0 Λ N p' = T.ph N a := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a)), hV 1 _ _ ?_, Or.inr fun x => ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ph =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) p' :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hgV)
    rw [mapDomain_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, e]
  · obtain ⟨hD, -, -, hU, -⟩ := m.ρ_maps N
    have e : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 * q1El (T.ph N a) ((A.A N).U a)) := by
      have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))).2 1
      rw [hD, lam_dom, mapRingHom_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, hp', funext (hU a)] at h1
      exact h1.symm
    rw [e]
    exact (A.m N).rel1 a _ x
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mapDomain_partial_charpoly_power_zero {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (φ : G →* H) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single (φ h) 1 * q2El (φ ph) (φ ta) u i y := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (φ g) c := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapRingHom_single_mul_partial_charpoly_element {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single h 1 * q2El ph ta (fun k => f (u k)) i (f y) := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem comap_tr {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

theorem UpperTheory.V.Pa.Core.t3Q2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (i : Fin n) (ph ta h : Ph0 Λ), πo0 Λ ph = Λ.ph a → πo0 Λ ta = Λ.ta a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph ta (W.t.U a) i (W.t.y a i)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a i ph ta h hph hta j
  obtain ⟨V, hV0, hV⟩ := UpperTheory.V.Pa.Core.phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V, Λ.ta_lim V] with N hk h1 h2
  have lift : ∀ (g : Ph0 Λ) (x : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (x : (T.GN N).Γ) (b : Λ.G.Γ) →
      πo0 Λ g = b → ∃ g' : Ph0 Λ, πN0 Λ N g' = x ∧
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g = QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g' := by
    intro g x b hc hg
    obtain ⟨g', e, hv⟩ := (UpperTheory.V.Pa.Core.closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (g : Λ.Ph) hc
      (congrArg Subtype.val hg)
    have hm : g' ∈ Ph0 Λ := by
      have := (Ph0 Λ).mul_mem g.2 (hV0 hv)
      rwa [mul_inv_cancel_left] at this
    exact ⟨⟨g', hm⟩, Subtype.ext e, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)⟩
  obtain ⟨ph', e1, q1⟩ := lift ph _ _ (h1 a) hph
  obtain ⟨ta', e2, q2⟩ := lift ta _ _ (h2 a) hta
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i)), ?_, Or.inr fun x => ?_⟩
  · apply hV 1
    rw [mapDomain_partial_charpoly_power_zero, mapDomain_partial_charpoly_power_zero, q1, q2]
  · obtain ⟨hD, -, -, hU, hy⟩ := m.ρ_maps N
    have key : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 *
          q2El (T.ph N a) (T.ta N a) ((A.A N).U a) i ((A.A N).s (MvPowerSeries.X (a, i)))) := by
      have h3 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))).2 1
      refine h3.symm.trans ?_
      rw [hD, mapRingHom_single_mul_partial_charpoly_element, hy a i, funext (hU a)]
      refine (comap_tr _ _ _).trans ?_
      rw [mapDomain_partial_charpoly_power_zero, e1, e2]
    rw [key]
    exact (A.m N).rel2 a i _ x
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tr_zero {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : (MonoidAlgebra.single (1 : G) (Polynomial.X : Polynomial A))
      = (Polynomial.X : Polynomial A) • (1 : MonoidAlgebra (Polynomial A) G) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
  have hchi : D.chi 0 = Polynomial.X ^ n := by
    simp only [GDet.chi, map_zero, sub_zero]
    rw [h1, D.homog, map_one, mul_one]
  simp only [GDet.tr, GDet.lam, hchi, Polynomial.coeff_X_pow]
  rw [if_neg (by omega)]
  simp

theorem UpperTheory.V.Pa.Core.patched_trace_single_mul_sub_one_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ∀ (h k : Ph0 Λ), πo0 Λ k = 1 → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn _ h k hk j
  obtain ⟨V, hVle, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  refine (Λ.ker_lim V).mono fun N hN => ?_
  have hk1 : Λ.πo (k : Λ.Ph) = 1 := congrArg Subtype.val hk
  have hkmem : (k : Λ.Ph) ∈ (Λ.π N).ker ⊔ (V.toOpenSubgroup : Subgroup Λ.Ph) := by
    rw [hN]
    exact Subgroup.mem_sup_left hk1
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkmem
  have haPh : a ∈ Ph0 Λ := by
    have : a = (k : Λ.Ph) * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact (Ph0 Λ).mul_mem k.2 ((Ph0 Λ).inv_mem (hVle hb))
  set k' : Ph0 Λ := ⟨a, haPh⟩ with hk'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)), ?_, Or.inl ?_⟩
  · have hq : (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))) k
        = QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ)) k' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((k⁻¹ * k' : Ph0 Λ) : Λ.Ph) = b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
        rw [← hab]
        group
      rw [this]
      exact inv_mem hb
    have hxy : (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1))
        = (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, hq]
    exact hV 1 _ _ hxy
  · have hπ : πN0 Λ N k' = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have hmaps := (m.ρ_maps N).1
    have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))).2 1
    have hy : (MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
        = MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1) := by
      simp
    have h2 := (comap_lam n _ _ _ (πN0 Λ N) (A.A N).p.D).2.2.1
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
    have h3 : (MonoidAlgebra.mapDomainRingHom (A.A N).R (πN0 Λ N))
        (MonoidAlgebra.single h (1 : (A.A N).R) * (MonoidAlgebra.single k' (1 : (A.A N).R) - 1)) = 0 := by
      rw [map_mul, map_sub, map_one]
      simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hπ]
      rw [← MonoidAlgebra.one_def, sub_self, mul_zero]
    calc m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)))
        = (m.ρ N).toRingHom (W.t.D.lam 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := rfl
      _ = (W.t.D.map (m.ρ N).toRingHom).lam 1 ((MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := h1.symm
      _ = ((A.A N).p.D.comap (πN0 Λ N)).tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
          rw [hy, hmaps]
          rfl
      _ = 0 := by rw [h2, h3]; exact tr_zero _ hn
end
