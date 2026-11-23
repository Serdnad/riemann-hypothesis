module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle001
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle008
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ar_family {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ (m : ℕ) (x : M), (∀ s, f s x ∈ I ^ (m + c) • (⊤ : Submodule A M')) →
      ∀ φ : M →ₗ[A] A, (∀ y, (∀ s, f s y = 0) → φ y = 0) → φ x ∈ I ^ m := by
  classical
  have hfg : (Submodule.span A (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let Φ : M →ₗ[A] (Fin n → M') := LinearMap.pi v
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I Φ
  have key : ∀ {ι : Type} (g : ι → M →ₗ[A] M') (N : Submodule A M') (x : M), (∀ i, g i x ∈ N) →
      ∀ u ∈ Submodule.span A (Set.range g), u x ∈ N := by
    intro ι g N x hx u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; exact hx i
    | zero => simp
    | add a b _ _ ha hb => exact N.add_mem ha hb
    | smul r a _ ha => exact N.smul_mem r ha
  refine ⟨c, fun m x hx φ hφ => ?_⟩
  have h0 : x ∈ (I ^ (m + c) • (⊤ : Submodule A (Fin n → M'))).comap Φ := by
    have h1 : ∀ i, v i x ∈ I ^ (m + c) • (⊤ : Submodule A M') := fun i =>
      key f _ x hx _ (hv ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [Submodule.mem_comap, ← Finset.univ_sum_single (Φ x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : LinearMap.single A (fun _ : Fin n => M') i (v i x) ∈
        (I ^ (m + c) • (⊤ : Submodule A M')).map (LinearMap.single A (fun _ : Fin n => M') i) :=
      Submodule.mem_map_of_mem (h1 i)
    rw [Submodule.map_smul''] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  have hle : LinearMap.ker Φ ⊔ I ^ m • (⊤ : Submodule A M) ≤ Submodule.comap φ (I ^ m : Ideal A) := by
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun a ha y _ => ?_)
    · have h1 : ∀ i, v i y ∈ (⊥ : Submodule A M') := fun i => congrFun (LinearMap.mem_ker.mp hy) i
      rw [Submodule.mem_comap, hφ y fun s => key v ⊥ y h1 (f s) (hv ▸ Submodule.subset_span ⟨s, rfl⟩)]
      exact zero_mem _
    · rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ha
  exact hle (hc m h0)

private theorem dd_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) : c • y = DD.C c * y := rfl

private theorem dd_finite (A : Type) [CommRing A] [IsNoetherianRing A] (g : ℕ) : Module.Finite A (DD A g) := by
  let f : DD A g →ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
    { toFun := DD.equiv
      map_add' := fun _ _ => rfl
      map_smul' := fun c y => by
        ext <;> simp [dd_smul, DD.equiv] }
  exact Module.Finite.of_injective f DD.equiv.injective

private theorem dd_ker {A : Type} [CommRing A] {g : ℕ} (s : A) (y : DD A g)
    (hy : DD.map g (Ideal.Quotient.mkₐ A (Ideal.span {s})) y = 0) : ∃ y' : DD A g, y = s • y' := by
  have key : ∀ a : A, Ideal.Quotient.mkₐ A (Ideal.span {s}) a = 0 → ∃ b, a = s * b := fun a ha =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
  obtain ⟨a, ha⟩ := key y.a (congrArg DD.a hy)
  choose b hb using fun j => key (y.ep j) (congrFun (congrArg DD.ep hy) j)
  choose b' hb' using fun j => key (y.ep' j) (congrFun (congrArg DD.ep' hy) j)
  obtain ⟨d, hd⟩ := key y.eta (congrArg DD.eta hy)
  refine ⟨⟨a, b, b', d⟩, ?_⟩
  ext <;> simp [dd_smul, ha, hb, hb', hd]

private theorem exists_antisymmetric_lift_of_section {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ} (f : A →ₐ[A] X)
    (σ : X →+ A) (hσ : ∀ y, f (σ y) = y) (Y : Matrix (Fin n) (Fin n) (DD X g)) (hY : Y ∈ W1 n A X g a)
    (hT : Yᵀ = -Y) : ∃ Y' ∈ W1 n A A g a, Y'ᵀ = -Y' ∧ Y'.map (DD.map g f) = Y := by
  let S : DD X g → DD A g := fun y => ⟨σ y.a, fun j => σ (y.ep j), fun j => σ (y.ep' j), σ y.eta⟩
  have hS : ∀ (b1 b2 b3 b4 : Bool) y, y ∈ ddPart A X g b1 b2 b3 b4 → S y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp [S, h1 e]
    · funext j; simp [S, h2 e]
    · funext j; simp [S, h3 e]
    · simp [S, h4 e]
  refine ⟨Y.map S, fun i j => ⟨fun e => hS _ _ _ _ _ ((hY i j).1 e), fun e => hS _ _ _ _ _ ((hY i j).2 e)⟩, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have e : Y j i = -Y i j := congrFun (congrFun hT i) j
    show S (Y j i) = -S (Y i j)
    rw [e]
    ext <;> simp [S]
  · refine Matrix.ext fun i j => ?_
    show DD.map g f (S (Y i j)) = Y i j
    ext <;> simp [S, hσ]

private theorem map_first_order_lift_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {X : Type} [CommRing X]
    [Algebra x.A X] (f : x.A →ₐ[x.A] X) (g : F.G₀) : (k.ρ1 x.A g).map (DD.map k.g f) = k.ρ1 X g := by
  have e1 : (x.ρX (DD x.A k.g) g).map (DD.map k.g f) = x.ρX (DD X k.g) g :=
    Matrix.ext fun i j => (DD.map k.g f).commutes _
  have e2 : (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (DD.map k.g f) =
      DD.epM fun j => (k.κ j g).map (algebraMap x.A X) := by
    refine Matrix.ext fun i j => ?_
    refine DD.ext (map_zero f) (funext fun r => f.commutes _) (funext fun r => map_zero f) (map_zero f)
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, e1, Matrix.map_add _ (map_add _), e2, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem exists_section (K : Type) [Field K] (I : Ideal (PowerSeries K)) :
    ∃ σ : (PowerSeries K ⧸ I) →+ PowerSeries K, ∀ y, Ideal.Quotient.mkₐ (PowerSeries K) I (σ y) = y := by
  obtain ⟨σ, hσ⟩ := (Ideal.Quotient.mkₐ K I).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective)
  exact ⟨σ.toAddMonoidHom, fun y => LinearMap.congr_fun hσ y⟩

theorem UpperTheory.V.Pa.coefficients_bounded_of_selmer_boundary :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (∀ i, z i ∈ Sel1 h x.A k) → (∀ c : Fin e → x.A, ∑ i, c i • z i ∈ Bd1 h x.A k → c = 0) → ∃ C : ℕ, ∀ (m : ℕ) (c : Fin e → x.A), (fun g => ((∑ i, c i • z i) g).map (x.redD k.g m)) ∈ Bd1 h (x.Am m) k → ∀ i, c i ∈ Ideal.span {x.t ^ (m - C)} := by
  intro l _ L G G0 h n x k e z _ _ hind
  haveI := dd_finite x.A k.g
  let V : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {Y | Y ∈ W1 n x.A x.A k.g x.a ∧ Yᵀ = -Y}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [transpose_add, ha.2, hb.2, neg_add]⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      smul_mem' := fun c Y hY => ⟨Submodule.smul_mem _ c hY.1, by rw [transpose_smul, hY.2, smul_neg]⟩ }
  let f : G.G₀ → ((Fin e → x.A) × V) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g =>
    { toFun := fun p => (∑ i, p.1 i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) p.2 g
      map_add' := fun p q => by
        simp only [dY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add,
          Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [dY, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
          Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    inferInstanceAs (Module.Finite x.A (Fin n → Fin n → DD x.A k.g))
  haveI : Module.Finite x.A V := Module.Finite.of_injective V.subtype V.subtype_injective
  obtain ⟨C, hC⟩ := ar_family (Ideal.span {x.t}) f
  refine ⟨C, fun m c hc i => ?_⟩
  rcases le_total m C with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨m, rfl⟩ : ∃ r, m = r + C := ⟨m - C, by omega⟩
  obtain ⟨Y, hY, hT, hYe⟩ := hc
  obtain ⟨σ, hσ⟩ := exists_section x.K (Ideal.span {x.t ^ (m + C)})
  obtain ⟨Y', hY', hT', rfl⟩ := exists_antisymmetric_lift_of_section _ σ hσ Y hY hT
  rw [Nat.add_sub_cancel, ← Ideal.span_singleton_pow]
  refine hC m (c, ⟨Y', hY', hT'⟩) (fun g => ?_) ((LinearMap.proj i).comp (LinearMap.fst _ _ _)) fun p hp => ?_
  · have h0 : (f g (c, ⟨Y', hY', hT'⟩)).map (x.redD k.g (m + C)) = 0 := by
      show ((∑ i, c i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y' g).map (x.redD k.g (m + C)) = 0
      rw [Matrix.map_sub _ (map_sub _), congrFun hYe g, sub_eq_zero, dY, dY, Matrix.map_sub _ (map_sub _),
        Matrix.map_mul, Matrix.map_mul, map_first_order_lift_eq, map_first_order_lift_eq]
    choose Z hZ using fun a b => dd_ker (x.t ^ (m + C)) _ (congrFun (congrFun h0 a) b)
    have h1 : f g (c, ⟨Y', hY', hT'⟩) = x.t ^ (m + C) • Matrix.of Z := Matrix.ext hZ
    rw [h1, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  · exact congrFun (hind p.1 ⟨p.2, p.2.2.1, p.2.2.2, funext fun g => sub_eq_zero.1 (hp g)⟩) i
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.elt_lim :
    ∀ (Ph B : Type) [Group Ph] [TopologicalSpace Ph] [IsTopologicalGroup Ph] [CompactSpace Ph] [TotallyDisconnectedSpace Ph] [Group B] (Γ : ℕ → Type) [∀ N, Group (Γ N)] (π : ∀ N, Ph →* Γ N) (πo : Ph →* B) (U : Ultrafilter ℕ) (a : ∀ N, Γ N), (∀ N, Function.Surjective (π N)) → ∃ b : B, ∀ V : OpenNormalSubgroup Ph, ∀ᶠ N in (U : Filter ℕ), Close (π N) πo V.toSubgroup (a N) b := by
  intro Ph B _ _ _ _ _ _ Γ _ π πo U a hπ
  choose g hg using fun N => hπ N (a N)
  obtain ⟨b, hb⟩ := (exists_lim_elt Ph ℕ U fun N => (π N).ker).1 g
  refine ⟨πo b, fun V => (hb V).mono fun N h => ⟨g N, b, hg N, rfl, ?_⟩⟩
  simpa using V.toSubgroup.inv_mem h
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem isOpen_map_of_ker_le {P Z : Type} [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Z] [TopologicalSpace Z] [T2Space Z] (f : P →* Z) (hf : Continuous f) (hs : Function.Surjective f)
    (V : Subgroup P) (hV : IsOpen (V : Set P)) (hk : f.ker ≤ V) : IsOpen (V.map f : Set Z) := by
  rw [← (hf.isClosedMap.isQuotientMap hf hs).isOpen_preimage]
  have : f ⁻¹' (V.map f : Set Z) = V := by
    rw [← Subgroup.coe_comap, Subgroup.comap_map_eq_self hk]
  rw [this]; exact hV

theorem UpperTheory.V.Pa.ker_oo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T), T.ProL → Λ.h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure := by
  intro l _ L G0 T Λ hT x hx
  set K := (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure with hK
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  refine (totallyDisconnected_quot Λ.G.Γ K (Subgroup.isClosed_topologicalClosure _)).2 x fun O => ?_
  haveI := O.isNormal'
  set W : Subgroup Λ.G.Γ := K ⊔ O.toSubgroup with hW
  haveI hWn : W.Normal := Subgroup.sup_normal _ _
  have hWo : IsOpen (W : Set Λ.G.Γ) := Subgroup.isOpen_mono (le_sup_right : O.toSubgroup ≤ W) O.isOpen'
  have hta : ∀ j, (Λ.ta j : Λ.G.Γ) ∈ W := fun j =>
    Subgroup.mem_sup_left (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩))
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := W.comap Λ.πo, isOpen' := hWo.preimage Λ.πo_cont, isNormal' := hWn.comap _ }
  have hVn : V.toSubgroup.Normal := V.isNormal'
  have hVo : IsOpen (V.toSubgroup : Set Λ.Ph) := V.isOpen'
  have hko : Λ.πo.ker ≤ V.toSubgroup := fun g hg => by
    show Λ.πo g ∈ W
    rw [MonoidHom.mem_ker.1 hg]; exact W.one_mem
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG0 : TopFG G0.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 G0.Γ (Λ.h.p.comp Λ.πo) (Λ.h.cont.comp Λ.πo_cont)
    (Λ.h.surj.comp Λ.πo_surj)
  have hidx : V.toSubgroup.index ≠ 0 := by
    haveI : Finite (Λ.Ph ⧸ V.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hVo
    exact Subgroup.index_ne_zero_of_finite
  have hfin := (finite_hom_of_topFG G0.Γ hG0).2.2 _ hidx
  have hall : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ A ∈ {H : Subgroup G0.Γ | IsOpen (H : Set G0.Γ) ∧ H.index = V.toSubgroup.index},
      A.Normal → ∀ g, (T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹ ∈ A := by
    rw [hfin.eventually_all]
    intro A hA
    by_cases hn : A.Normal
    · exact (Λ.p_lim { toSubgroup := A, isOpen' := hA.1, isNormal' := hn }).mono fun N h _ => h
    · exact Eventually.of_forall fun N h => absurd h hn
  obtain ⟨N, h1, h2, h3⟩ := ((Λ.ker_lim V).and ((Λ.ta_lim V).and hall)).exists
  have hkN : (Λ.π N).ker ≤ V.toSubgroup := le_sup_left.trans (h1.le.trans (sup_le hko le_rfl))
  haveI hVNn : (V.toSubgroup.map (Λ.π N)).Normal := hVn.map _ (Λ.π_surj N)
  have hVNo := isOpen_map_of_ker_le (Λ.π N) (Λ.π_cont N) (Λ.π_surj N) _ hVo hkN
  have hkh : (T.h N).p.ker ≤ V.toSubgroup.map (Λ.π N) := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hVNo))
    rw [hT.2 N, sup_bot_eq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, g', hg, hg', hgg⟩ := h2 j
    have hg'V : g' ∈ V.toSubgroup := by
      show Λ.πo g' ∈ W
      rw [hg']; exact hta j
    refine ⟨g, ?_, hg⟩
    have := mul_mem hg'V (inv_mem hgg)
    simpa using this
  let f : Λ.Ph →* G0.Γ := (T.h N).p.comp (Λ.π N)
  have hfs : Function.Surjective f := (T.h N).surj.comp (Λ.π_surj N)
  have hfk : f.ker ≤ V.toSubgroup := fun g hg => by
    rw [← Subgroup.comap_map_eq_self hkN]
    exact hkh hg
  have hAo := isOpen_map_of_ker_le f ((T.h N).cont.comp (Λ.π_cont N)) hfs _ hVo hfk
  have hAi : (V.toSubgroup.map f).index = V.toSubgroup.index := by
    rw [← Subgroup.index_comap_of_surjective _ hfs, Subgroup.comap_map_eq_self hfk]
  obtain ⟨g, rfl⟩ := Λ.πo_surj x
  have h4 := h3 _ ⟨hAo, hAi⟩ (hVn.map _ hfs) g
  rw [MonoidHom.mem_ker.1 hx, inv_one, mul_one] at h4
  have h5 : g ∈ (V.toSubgroup.map f).comap f := h4
  rw [Subgroup.comap_map_eq_self hfk] at h5
  exact h5
end
