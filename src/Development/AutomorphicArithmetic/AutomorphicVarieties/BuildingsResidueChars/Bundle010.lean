module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle003
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open UpperTheory.V.Af.CuspFin

private theorem glRel_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel (fun a b => f (X a b)) := by
  intro i j k l
  have := congrArg f (h i j k l)
  simpa [apply_ite f] using this

private theorem comm_LR {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (a : A) (b : B) :
    Commute ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) a)
      ((Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) b) := by
  simp [Commute, SemiconjBy]

private theorem map_cap {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) : (capAlg E).map f ≤ capAlg F := by
  unfold capAlg
  rw [AlgHom.map_adjoin]
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨_, ⟨v, u, rfl⟩, rfl⟩
  exact ⟨e v, u, by rw [map_qdet, h]⟩

private theorem map_gen {ι κ A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : ι → Fin n → Fin n → A) (F : κ → Fin n → Fin n → B) (e : ι → κ)
    (hg : Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} = ⊤)
    (h : ∀ v, F (e v) = fun i j => f (E v i j)) (a : A) :
    f a ∈ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
  have : (Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j}).map f ≤ Algebra.adjoin ℂ {z | ∃ v i j, z = F v i j} := by
    rw [AlgHom.map_adjoin]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨_, ⟨v, i, j, rfl⟩, rfl⟩
    exact ⟨e v, i, j, by rw [h]⟩
  exact this ⟨a, by rw [hg]; trivial, rfl⟩

theorem UpperTheory.capelliAlgebra_map_of_glRelations :
    ∀ (n : ℕ) (ι κ : Type), UpperTheory.V.Af.CuspFin.HasUniv ι n → UpperTheory.V.Af.CuspFin.HasUniv κ n → UpperTheory.V.Af.CuspFin.HasUniv (ι ⊕ κ) n := by
  rintro n ι κ ⟨A, _, _, E, hE⟩ ⟨B, _, _, F, hF⟩
  let L : A →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeLeft
  let R : B →ₐ[ℂ] TensorProduct ℂ A B := Algebra.TensorProduct.includeRight
  let G : ι ⊕ κ → Fin n → Fin n → TensorProduct ℂ A B :=
    Sum.elim (fun v i j => L (E v i j)) (fun v i j => R (F v i j))
  refine ⟨TensorProduct ℂ A B, inferInstance, inferInstance, G, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro (v | v)
    · exact glRel_map L (hE.rel.1 v)
    · exact glRel_map R (hF.rel.1 v)
  · rintro (v | v) (w | w) hvw i j k l
    · exact (hE.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map L
    · exact comm_LR _ _
    · exact (comm_LR _ _).symm
    · exact (hF.rel.2 v w (fun h => hvw (congrArg _ h)) i j k l).map R
  · refine eq_top_iff.2 fun z hz => ?_
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a b =>
      have : a ⊗ₜ[ℂ] b = L a * R b := by simp [L, R]
      rw [this]
      exact mul_mem (map_gen L E G Sum.inl hE.gen (fun _ => rfl) a) (map_gen R F G Sum.inr hF.gen (fun _ => rfl) b)
    | add x y hx hy => exact add_mem hx hy
  · intro C _ _ H hH
    obtain ⟨f, hf⟩ := hE.univ C (fun v => H (Sum.inl v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inl_injective h)⟩
    obtain ⟨g, hg⟩ := hF.univ C (fun v => H (Sum.inr v))
      ⟨fun v => hH.1 _, fun v w hvw => hH.2 _ _ fun h => hvw (Sum.inr_injective h)⟩
    have hc : ∀ a b, Commute (f a) (g b) := by
      intro a b
      have ha := map_gen f E (fun v => H (Sum.inl v)) id hE.gen (fun v => by funext i j; simp [hf]) a
      have hb := map_gen g F (fun v => H (Sum.inr v)) id hF.gen (fun v => by funext i j; simp [hg]) b
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
      rintro _ ⟨w, k, l, rfl⟩
      refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
      rintro _ ⟨v, i, j, rfl⟩
      exact hH.2 _ _ Sum.inr_ne_inl _ _ _ _
    refine ⟨Algebra.TensorProduct.lift f g hc, ?_⟩
    rintro (v | v) i j
    · simp [G, L, hf]
    · simp [G, R, hg]
  · refine (UpperTheory.center_tensorProduct_le_sup_map_center A B).trans (sup_le ?_ ?_)
    · exact (Subalgebra.map_mono hE.centre).trans (map_cap L E G Sum.inl fun _ => rfl)
    · exact (Subalgebra.map_mono hF.centre).trans (map_cap R F G Sum.inr fun _ => rfl)
end

section

open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

theorem UpperTheory.exists_free_lattice_spanning_ordinary_part :
    ∀ (O Ω V ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] [Fintype ι] (C : Submodule Ω V) (T : Module.End Ω V) (ev : V →ₗ[Ω] (ι → Ω)), Function.Injective (algebraMap O Ω) → Set.BijOn ev C Set.univ → (∀ F ∈ C, T F ∈ C) → (∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∀ i, ev (T F) i ∈ mIm O Ω 0) → ∃ S : Submodule O V, Module.Free O S ∧ (⨆ μ : {μ : Ω // IsIntUnit O μ}, C ⊓ T.maxGenEigenspace μ.1) = Submodule.span Ω (S : Set V) ∧ (∀ F ∈ S, F ∈ C ∧ (∀ i, ev F i ∈ mIm O Ω 0) ∧ ∀ k : ℕ, ∃ n : ℕ, ∀ i, ev ((T ^ (n + 1)) F - F) i ∈ mIm O Ω k) ∧ ∀ F ∈ C, (∀ i, ev F i ∈ mIm O Ω 0) → ∃ F' ∈ S, ∀ k : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, ev ((T ^ j.factorial) F - F') i ∈ mIm O Ω k := by
  intro O Ω V ι _ _ _ _ _ _ _ _ _ _ C T ev hinj hbij hTC hint
  haveI : IsAdicComplete (maximalIdeal O) O := IsCNL.complete
  haveI : Finite (ResidueField O) := IsCNL.finite
  obtain ⟨hadm, hfin⟩ := ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)
  have hfin' := hfin ‹_›
  set A := algebraMap O Ω with hA
  let evC : C →ₗ[Ω] (ι → Ω) := ev ∘ₗ C.subtype
  have hevC : Function.Bijective evC := by
    refine ⟨fun x y hxy => Subtype.ext (hbij.injOn x.2 y.2 hxy), fun w => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hbij.surjOn (Set.mem_univ w)
    exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective evC hevC
  let g : (ι → Ω) →ₗ[Ω] V := C.subtype ∘ₗ e.symm.toLinearMap
  have hgC : ∀ w, g w ∈ C := fun w => (e.symm w).2
  have hevg : ∀ w, ev (g w) = w := fun w => e.apply_symm_apply w
  have hgev : ∀ F ∈ C, g (ev F) = F := fun F hF => by
    have : e ⟨F, hF⟩ = ev F := rfl
    show ((e.symm (ev F) : C) : V) = F
    rw [← this, e.symm_apply_apply]
  have hginj : Function.Injective g := fun a b h => by rw [← hevg a, ← hevg b, h]
  let T' : Module.End Ω (ι → Ω) := ev ∘ₗ T ∘ₗ g
  have hgT : ∀ w, g (T' w) = T (g w) := fun w => hgev _ (hTC _ (hgC w))
  let jL : (ι → O) →ₗ[O] (ι → Ω) := LinearMap.pi (fun i => (Algebra.linearMap O Ω) ∘ₗ LinearMap.proj i)
  have hjL : ∀ v i, jL v i = A (v i) := fun v i => rfl
  have hjinj : Function.Injective jL := fun v w h => funext fun i => hinj (by rw [← hjL, ← hjL, h])
  have hmem0 : ∀ x : O, A x ∈ mIm O Ω 0 := fun x => mem_mIm.2 ⟨x, by simp, rfl⟩
  have hint' : ∀ v : ι → O, ∀ i, ∃ x : O, A x = T' (jL v) i := by
    intro v i
    have h1 : ∀ i, ev (g (jL v)) i ∈ mIm O Ω 0 := fun i => by rw [hevg]; exact hmem0 _
    obtain ⟨x, -, hx⟩ := mem_mIm.1 (hint _ (hgC _) h1 i)
    exact ⟨x, hx⟩
  choose f0 hf0 using hint'
  let T₀ : Module.End O (ι → O) :=
    { toFun := f0
      map_add' := fun v w => funext fun i => hinj (by
        simp only [Pi.add_apply, map_add (f := _), hf0])
      map_smul' := fun c v => funext fun i => hinj (by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, hf0, RingHom.id_apply]
        rw [map_smul, ← algebraMap_smul Ω c (jL v), map_smul, Pi.smul_apply, smul_eq_mul]) }
  have hT₀ : ∀ v, T' (jL v) = jL (T₀ v) := fun v => funext fun i => (hf0 v i).symm
  have key := UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces O Ω ι T₀ T' (fun v => hT₀ v)
  let L : (ι → O) →ₗ[O] V := (g.restrictScalars O) ∘ₗ jL
  have hLinj : Function.Injective L := hginj.comp hjinj
  have hpow : ∀ m w, g ((T' ^ m) w) = (T ^ m) (g w) := pow_intertwine (U := T') (U' := T) (f := g) hgT
  have hpow0 : ∀ m u, jL ((T₀ ^ m) u) = (T' ^ m) (jL u) :=
    pow_intertwine (U := T₀) (U' := T') (f := jL) (fun u => (hT₀ u).symm)
  have hcoord : ∀ k (x : ι → O), x ∈ maximalIdeal O ^ k • (⊤ : Submodule O (ι → O)) → ∀ i, x i ∈ maximalIdeal O ^ k := by
    intro k x hx i
    have := map_mem_smul_top (LinearMap.proj (R := O) (φ := fun _ : ι => O) i) _ hx
    simpa using this
  refine ⟨(ordPart T₀).map L, ?_, ?_, ?_, ?_⟩
  · haveI := (ordProjective hadm T₀).1 inferInstance
    haveI := (ordProjective hadm T₀).2 inferInstance
    haveI : Module.Free O (ordPart T₀) := Module.free_of_flat_of_isLocalRing
    exact Module.Free.of_equiv (Submodule.equivMapOfInjective L hLinj _)
  · have key' : (⨆ μ : {μ : Ω // IsIntUnit O μ}, T'.maxGenEigenspace μ.1) =
        Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O))) := key
    have hspan : Submodule.span Ω (((ordPart T₀).map L : Submodule O V) : Set V) =
        (Submodule.span Ω (jL '' (ordPart T₀ : Set (ι → O)))).map g := by
      rw [← Submodule.span_image, Submodule.map_coe, Set.image_image]
      rfl
    have heig : ∀ μ : Ω, C ⊓ T.maxGenEigenspace μ = (T'.maxGenEigenspace μ).map g := by
      intro μ
      have hpowμ : ∀ (k : ℕ) (w : ι → Ω), g (((T' - μ • (1 : Module.End Ω (ι → Ω))) ^ k) w) =
          ((T - μ • (1 : Module.End Ω V)) ^ k) (g w) :=
        pow_intertwine (U := T' - μ • 1) (U' := T - μ • 1) (f := g) (fun w => by simp [hgT])
      ext x
      constructor
      · rintro ⟨hxC, hx⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
        refine ⟨ev x, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, hginj ?_⟩, hgev x hxC⟩
        rw [hpowμ, hgev x hxC, hk, map_zero]
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
        exact ⟨hgC w, (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [← hpowμ, hk, map_zero]⟩⟩
    rw [hspan, ← key', Submodule.map_iSup]
    exact iSup_congr fun μ => heig μ.1
  · rintro F ⟨v, hv, rfl⟩
    refine ⟨hgC _, fun i => ?_, fun k => ?_⟩
    · show ev (g (jL v)) i ∈ _
      rw [hevg]
      exact hmem0 _
    · obtain ⟨n, hn⟩ := (ordPer hadm hfin' T₀ v).1 hv k
      refine ⟨n, fun i => ?_⟩
      show ev ((T ^ (n + 1)) (g (jL v)) - g (jL v)) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ hn i, rfl⟩
  · intro F hF hFi
    choose v _ hv using fun i => mem_mIm.1 (hFi i)
    have hFv : F = g (jL v) := by
      rw [← hgev F hF]
      congr 1
      funext i
      exact (hv i).symm
    refine ⟨L (ordProj (maximalIdeal O) T₀ v), ⟨_, ?_, rfl⟩, fun k => ?_⟩
    · rw [← (ordExists hadm T₀).2.1]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨N, hN⟩ := (ordFactLim hadm hfin' T₀ _).2 rfl k
      refine ⟨N, fun j hj i => ?_⟩
      rw [hFv]
      show ev ((T ^ j.factorial) (g (jL v)) - g (jL (ordProj _ T₀ v))) i ∈ _
      rw [← hpow, ← hpow0, ← map_sub, hevg, ← map_sub, hjL]
      exact mem_mIm.2 ⟨_, hcoord _ _ (hN j hj v) i, rfl⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_iwahori_character_extending_torus_character :
    ∀ (G : Type) [Group G] (I : Iwa G) (B : Type) [CommGroup B] (c : ℕ) (φ : I.T →* B), (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → ∃ ψ : I.Iw c →* B, ∀ b : I.Iw c, ((b : G) ∈ I.N → ψ b = 1) ∧ ((b : G) ∈ I.Nm c → ψ b = 1) ∧ ∀ hb : (b : G) ∈ I.T, ψ b = φ ⟨b, hb⟩ := by
  intro G _ I B _ c φ hφ
  obtain ⟨tt, h1, htt⟩ := UpperTheory.exists_iwahori_torus_projection G I
  have hle : ∀ b ∈ I.Iw c, b ∈ I.Iw 0 := by
    intro b hb
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 hb
    exact (UpperTheory.V.Hi.iwMem G I 0 b).1.2 ⟨x, hx, t, ht, y, I.Nm_anti (Nat.zero_le c) hy, h⟩
  have key : ∀ b ∈ I.Iw 0, ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c,
      φ (tt (b * (x * t * y))) = φ (tt b) * φ t := by
    intro b hb x hx t y hy
    have hx0 : x ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 x).1.2 ⟨x, hx, 1, one_mem _, 1, one_mem _, by simp⟩
    have ht0 : (t : G) ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 t).1.2 ⟨1, one_mem _, t, t.2, 1, one_mem _, by simp⟩
    have hbx := mul_mem hb hx0
    obtain ⟨s, hs, e⟩ := (htt _ (mul_mem hbx ht0)).2.2 c y hy
    have e0 : b * (x * t * y) = b * x * t * y := by group
    rw [e0, e, map_mul, hφ s hs, mul_one, ((htt _ hbx).1 t).2, (htt b hb).2.1 x hx, map_mul]
  have key1 : ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c, φ (tt (x * t * y)) = φ t := by
    intro x hx t y hy
    have := key 1 (one_mem _) x hx t y hy
    rwa [one_mul, h1, map_one, one_mul] at this
  refine ⟨MonoidHom.mk' (fun b => φ (tt b)) ?_, fun b => ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩⟩
  · intro a b
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 b.2
    have e1 := key a (hle _ a.2) x hx ⟨t, ht⟩ y hy
    have e2 := key1 x hx ⟨t, ht⟩ y hy
    show φ (tt ((a : G) * b)) = φ (tt a) * φ (tt b)
    rw [h, e2]
    exact e1
  · simpa using key1 b hb 1 1 (one_mem _)
  · simpa using key1 1 (one_mem _) 1 b hb
  · simpa using key1 1 (one_mem _) ⟨b, hb⟩ 1 (one_mem _)
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_section_automorphicSpace_with_prescribed_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U : Subgroup X.Ub, X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v, s v ∈ X.Sp τ θ U ∧ (∀ i j, s v (x i) j = v (i, j)) ∧ ∀ k : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∀ y ∈ X.I.Nm c, X.rp A m y (s v) - s v ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U hF c N x hcov huniq
  unfold Iwa.ContChar at hθ
  obtain ⟨tt, htt1, htt⟩ := UpperTheory.exists_iwahori_torus_projection Gp X.I
  obtain ⟨s, hs⟩ := UpperTheory.exists_linear_section_automorphicFunctions_of_free Γ Ga Gp X A m τ θ U hF c N x hcov huniq tt
    (fun b hb t => ((htt b hb).1 t).1)
  have hN_le : X.I.N ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_left.trans le_sup_left
  have hT_le : X.I.T ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right.trans le_sup_left
  have hNm_le : X.I.Nm c ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right
  have hIw0 : X.I.Iw c ≤ X.I.Iw 0 := by
    unfold Iwa.Iw
    exact sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  have key : ∀ (k : ℕ) (a e w : A), e - 1 ∈ maximalIdeal A ^ k → a * (e * w) - a * w ∈ maximalIdeal A ^ k := by
    intro k a e w h
    rw [show a * (e * w) - a * w = (a * w) * (e - 1) by ring]
    exact Ideal.mul_mem_left _ _ h
  have hright : ∀ (γ : Γ) (i : Fin N) (u : X.Ub) (b y : Gp),
      X.glob γ * x i * ((u : Ga), b) * (1, y) = X.glob γ * x i * ((u : Ga), b * y) := by
    intro γ i u b y
    rw [mul_assoc]
    exact congrArg _ (Prod.ext (mul_one _) rfl)
  have hdiff : ∀ v (k c' : ℕ), c ≤ c' → (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → (θ t : A) - 1 ∈ maximalIdeal A ^ k) →
      ∀ y ∈ X.I.Nm c', ∀ g j, s v (g * (1, y)) j - s v g j ∈ maximalIdeal A ^ k := by
    intro v k c' hcc' hk y hy g j
    obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
    have hb0 : b ∈ X.I.Iw 0 := hIw0 hb
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hcc' hy
    obtain ⟨s0, hs0, hts⟩ := (htt b hb0).2.2 c' y hy
    have hby : b * y ∈ X.I.Iw c := mul_mem hb (hNm_le hyc)
    rw [hright, hs v γ i u hu (b * y) hby, hs v γ i u hu b hb, hts, map_mul, mul_inv, Units.val_mul, mul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply key
    have h := hk s0 hs0
    have hinv := Units.inv_mul (θ s0)
    have : (((θ s0)⁻¹ : Aˣ) : A) - 1 = -(((θ s0)⁻¹ : Aˣ) : A) * ((θ s0 : A) - 1) := by
      linear_combination hinv
    rw [this]
    exact Ideal.mul_mem_left _ _ h
  refine ⟨s, fun v => ⟨?_, ?_, ?_⟩⟩
  · unfold Frame.Sp Frame.Amb
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show (_ ∧ _ ∧ _ ∧ _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro γ' g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [show X.glob γ' * (X.glob γ * x i * ((u : Ga), b)) = X.glob (γ' * γ) * x i * ((u : Ga), b) by
          rw [map_mul]; simp only [mul_assoc], hs v _ i u hu b hb, hs v γ i u hu b hb]
      · unfold fixd
        show ∀ n ∈ X.I.N, _
        intro n hn
        funext g
        show s v (g * (1, n)) = s v g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * n) (mul_mem hb (hN_le hn)), hs v γ i u hu b hb,
          (htt b (hIw0 hb)).2.1 n hn]
      · intro t
        funext g
        show s v (g * (1, (t : Gp))) = _
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * t) (mul_mem hb (hT_le t.2)), Pi.smul_apply, hs v γ i u hu b hb,
          ((htt b (hIw0 hb)).1 t).2, map_mul, mul_inv, Units.val_mul,
          mul_comm (((θ (tt b))⁻¹ : Aˣ) : A), mul_smul]
      · intro k
        obtain ⟨c0, hc0⟩ := hθ k
        exact ⟨max c c0, fun y hy g j => hdiff v k (max c c0) (le_max_left _ _)
          (fun t ht => hc0 t (X.I.Tc_anti (le_max_right _ _) ht)) y hy g j⟩
    · unfold fixd
      show ∀ u' ∈ U, _
      intro u' hu'
      funext g
      rw [Frame.ra_apply]
      obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
      rw [show X.glob γ * x i * ((u : Ga), b) * ((u' : Ga), 1) =
            X.glob γ * x i * (((u * u' : X.Ub) : Ga), b) by
          rw [mul_assoc]; exact congrArg _ (Prod.ext rfl (mul_one _)),
        hs v γ i (u * u') (mul_mem hu hu') b hb, hs v γ i u hu b hb, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, show u' * (u * u')⁻¹ = u⁻¹ by group]
  · intro i j
    have e : x i = X.glob 1 * x i * (((1 : X.Ub) : Ga), (1 : Gp)) := by simp
    rw [e, hs v 1 i 1 U.one_mem 1 (X.I.Iw c).one_mem, htt1]
    simp
  · intro k hk y hy
    unfold Frame.valIn
    rw [Submodule.mem_pi]
    intro g _
    rw [Submodule.mem_pi]
    intro j _
    exact hdiff v k c le_rfl hk y hy g j
end

section

open IsLocalRing Matrix UpperTheory.V.Hi

private def repsRel {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub)
    (c : ℕ) : Setoid (Ga × Gp) where
  r g h := ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * h * ((u : Ga), b)
  iseqv :=
    { refl := fun g => ⟨1, 1, one_mem _, 1, one_mem _, by simp [Prod.mk_one_one]⟩
      symm := by
        rintro g h ⟨γ, u, hu, b, hb, rfl⟩
        refine ⟨γ⁻¹, u⁻¹, inv_mem hu, b⁻¹, inv_mem hb, ?_⟩
        have : (((u⁻¹ : X.Ub) : Ga), b⁻¹) = ((u : Ga), b)⁻¹ := rfl
        rw [this, map_inv]
        group
      trans := by
        rintro g h k ⟨γ, u, hu, b, hb, rfl⟩ ⟨γ', u', hu', b', hb', rfl⟩
        refine ⟨γ * γ', u' * u, mul_mem hu' hu, b' * b, mul_mem hb' hb, ?_⟩
        have : (((u' * u : X.Ub) : Ga), b' * b) = ((u' : Ga), b') * ((u : Ga), b) := rfl
        rw [this, map_mul]
        group }

theorem UpperTheory.exists_finite_iwahori_doubleCoset_representatives :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub), X.FinLevel U → ∀ c : ℕ, ∃ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) ∧ (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) := by
  intro Γ Ga Gp _ _ _ X U hU c
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).1
  haveI : Finite (Quotient (repsRel X U c)) := by
    refine Finite.of_surjective
      (fun p : s × (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) =>
        Quotient.mk (repsRel X U c) ((p.1 : Ga × Gp) * (1, (p.2.out : Gp)))) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.I.Iw c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
      refine ⟨(⟨x, hx⟩, ((⟨b, hb⟩ : X.I.Iw 0) : _ ⧸ _)), ?_⟩
      symm
      refine Quotient.sound ⟨γ, u, hu, ((m : X.I.Iw 0) : Gp)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 m.2), ?_⟩
      simp only [hm, Subgroup.coe_mul, mul_assoc, Prod.mk_mul_mk, one_mul, mul_inv_cancel, mul_one]
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (repsRel X U c))
  refine ⟨N, fun i => (e.symm i).out, fun g => ?_, fun i j γ u hu b hb h => ?_⟩
  · obtain ⟨γ, u, hu, b, hb, h⟩ := (repsRel X U c).symm (Quotient.mk_out (s := repsRel X U c) g)
    exact ⟨γ, e (Quotient.mk _ g), u, hu, b, hb, by simpa using h⟩
  · have h1 : Quotient.mk (repsRel X U c) (e.symm j).out = Quotient.mk (repsRel X U c) (e.symm i).out :=
      Quotient.sound ⟨γ, u, hu, b, hb, h⟩
    rw [Quotient.out_eq, Quotient.out_eq] at h1
    exact (e.symm.injective h1).symm
end
