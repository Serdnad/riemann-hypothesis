module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

open scoped TensorProduct in
private theorem UpperTheory.V.Pa.dual_functionals_finite_separating_surjective {R F N : Type} [CommRing R] [Field F] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (φ : R →+* F) (hs : Function.Surjective φ) (L : Submodule F (N →+ F))
    (hL : ∀ μ, μ ∈ L ↔ ∀ (b : R) y, μ (b • y) = φ b * μ y) :
    Module.Finite F L ∧ (∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N)) ∧
      ∀ ξ : Module.Dual F L, ∃ y : N, ∀ μ : L, (μ : N →+ F) y = ξ μ := by
  classical
  have hzero : ∀ μ ∈ L, ∀ t : Set N, Submodule.span R t = ⊤ → (∀ y ∈ t, μ y = 0) → μ = 0 := by
    intro μ hμ t ht h0
    refine AddMonoidHom.ext fun y => ?_
    show μ y = 0
    have hy : y ∈ Submodule.span R t := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact h0 x hx
    | zero => exact map_zero μ
    | add x z _ _ hx hz => rw [map_add (f := _), hx, hz, add_zero]
    | smul b x _ hx => rw [(hL μ).1 hμ b x, hx, mul_zero]
  have hfin : Module.Finite F L := by
    obtain ⟨n, s, hsp⟩ := Module.Finite.exists_fin (R := R) (M := N)
    let Φ : L →ₗ[F] (Fin n → F) :=
      { toFun := fun μ i => (μ : N →+ F) (s i)
        map_add' := fun μ ν => by ext i; rfl
        map_smul' := fun c μ => by ext i; rfl }
    refine Module.Finite.of_injective Φ ?_
    refine (injective_iff_map_eq_zero Φ).2 fun μ hμ => Subtype.ext ?_
    refine hzero _ μ.2 _ hsp ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun hμ i
  have hkill : ∀ y : N, (∀ μ ∈ L, μ y = 0) → y ∈ RingHom.ker φ • (⊤ : Submodule R N) := by
    intro y hy
    by_contra hny
    set K := RingHom.ker φ
    set P := K • (⊤ : Submodule R N)
    have ht : Module.IsTorsionBySet R (N ⧸ P) (K : Set R) :=
      (Module.isTorsionBySet_quotient_iff P _).2 fun x r hr =>
        Submodule.smul_mem_smul hr Submodule.mem_top
    letI : Module (R ⧸ K) (N ⧸ P) := ht.module
    let e := RingHom.quotientKerEquivOfSurjective hs
    letI : Module F (N ⧸ P) := Module.compHom (N ⧸ P) (e.symm : F →+* R ⧸ K)
    have hcomp : ∀ (b : R) (q : N ⧸ P), φ b • q = b • q := by
      intro b q
      show (e.symm (φ b)) • q = b • q
      rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hs b, RingEquiv.symm_apply_apply]
      exact Module.IsTorsionBySet.mk_smul ht b q
    have hq : Submodule.Quotient.mk (p := P) y ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual F (N ⧸ P), f (Submodule.Quotient.mk y) ≠ 0 := by
      by_contra! h
      exact hq ((Module.forall_dual_apply_eq_zero_iff F _).1 h)
    let μ : N →+ F := f.toAddMonoidHom.comp P.mkQ.toAddMonoidHom
    have hμ : μ ∈ L := (hL μ).2 fun b z => by
      show f (Submodule.Quotient.mk (b • z)) = φ b * f (Submodule.Quotient.mk z)
      rw [Submodule.Quotient.mk_smul, ← hcomp, map_smul, smul_eq_mul]
    exact hf (hy μ hμ)
  refine ⟨hfin, hkill, ?_⟩
  intro ξ
  haveI := hfin
  let ev : N → Module.Dual F L := fun y =>
    { toFun := fun μ => (μ : N →+ F) y
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule F (Module.Dual F L) :=
    { carrier := {a | ∃ y : N, ∀ μ : L, (μ : N →+ F) y = a μ}
      add_mem' := by
        rintro a b ⟨y, hy⟩ ⟨z, hz⟩
        exact ⟨y + z, fun μ => by rw [map_add (f := _), hy, hz]; rfl⟩
      zero_mem' := ⟨0, fun μ => by simp⟩
      smul_mem' := by
        rintro c a ⟨y, hy⟩
        obtain ⟨b, rfl⟩ := hs c
        exact ⟨b • y, fun μ => by rw [(hL _).1 μ.2, hy]; rfl⟩ }
  by_contra hξ
  change ξ ∉ W at hξ
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hξ inferInstance
  set μ := (Module.evalEquiv F L).symm f with hμdef
  have hμ0 : μ = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    have hm : f (ev y) ∈ W.map f := Submodule.mem_map_of_mem ⟨y, fun _ => rfl⟩
    rw [hfW, Submodule.mem_bot] at hm
    have := Module.apply_evalEquiv_symm_apply F L (ev y) f
    rw [← hμdef, hm] at this
    exact this
  have hfe : f = Module.evalEquiv F L μ := ((Module.evalEquiv F L).apply_symm_apply f).symm
  rw [hfe, hμ0, map_zero] at hf
  exact hf rfl

theorem UpperTheory.V.Pa.laDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.La ∧ (∀ y : S.U.N, (∀ μ ∈ S.La, μ y = 0) → y ∈ maximalIdeal S.Bh • (⊤ : Submodule S.Bh S.U.N)) ∧ ∀ ξ : Module.Dual S.F S.La, ∃ y : S.U.N, ∀ μ : S.La, (μ : S.U.N →+ S.F) y = ξ μ := by
  intro l _ S
  have hs : Function.Surjective S.rF := fun c => by
    obtain ⟨o, ho⟩ := S.oo_surj c
    exact ⟨_, ho⟩
  haveI := S.U.fin
  haveI hN : Module.Finite S.Bh S.U.N :=
    Module.Finite.of_surjective (Submodule.projectionOnto S.U.N 1 S.U.compl.symm)
      (Submodule.projectionOnto_surjective S.U.compl.symm)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Pa.dual_functionals_finite_separating_surjective S.rF hs S.La (fun μ => Iff.rfl)
  refine ⟨h1, fun y hy => ?_, h3⟩
  rw [← S.rF_ker]
  exact h2 y hy
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_of_univ {R F W : Type} [AddCommGroup R] [Field F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] (π : R →+ W) (T : Submodule F (R →+ F))
    (h1 : ∀ φ : Module.Dual F W, φ.toAddMonoidHom.comp π ∈ T)
    (h2 : ∀ α ∈ T, ∃ φ : Module.Dual F W, φ.toAddMonoidHom.comp π = α) :
    Module.Finite F T ∧ (∀ b, (∀ α ∈ T, α b = 0) → π b = 0) ∧
      ∀ ξ : Module.Dual F T, ∃ w : W, ∀ b, π b = w → ∀ α : T, (α : R →+ F) b = ξ α := by
  let Φ : Module.Dual F W →ₗ[F] T :=
    { toFun := fun φ => ⟨φ.toAddMonoidHom.comp π, h1 φ⟩
      map_add' := fun _ _ => Subtype.ext (by ext; simp)
      map_smul' := fun _ _ => Subtype.ext (by ext; simp) }
  have hΦ : Function.Surjective Φ := fun α => by
    obtain ⟨φ, e⟩ := h2 α.1 α.2
    exact ⟨φ, Subtype.ext e⟩
  refine ⟨Module.Finite.of_surjective Φ hΦ, fun b hb => ?_, fun ξ => ?_⟩
  · exact (Module.forall_dual_apply_eq_zero_iff F (π b)).1 fun φ => hb _ (h1 φ)
  · obtain ⟨w, hw⟩ := (Module.evalEquiv F W).surjective (ξ.comp Φ)
    refine ⟨w, fun b hb α => ?_⟩
    obtain ⟨φ, rfl⟩ := hΦ α
    have := LinearMap.congr_fun hw φ
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearMap.comp_apply] at this
    rw [← this, ← hb]
    rfl

private theorem tp_abs {O R F : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field F] [Algebra O R] [IsLocalHom (algebraMap O R)] (r : R →+* F) (hk : RingHom.ker r = maximalIdeal R)
    (hs : Function.Surjective (r.comp (algebraMap O R))) (I J : Ideal R)
    (hJ : J = (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 ⊔ I) (hI : I ≤ maximalIdeal R)
    (hJm : J ≤ maximalIdeal R) (T : Submodule F (R →+ F))
    (hT : ∀ α, α ∈ T ↔ (∀ b b', α (b * b') = r b * α b' + r b' * α b) ∧ (∀ o, α (algebraMap O R o) = 0) ∧
      ∀ b ∈ I, α b = 0) :
    Module.Finite F T ∧ (∀ b ∈ maximalIdeal R, (∀ α ∈ T, α b = 0) → b ∈ J) ∧
      ∀ ξ : Module.Dual F T, ∃ b ∈ maximalIdeal R, ∀ α : T, (α : R →+ F) b = ξ α := by
  have hm : ∀ b, b ∈ maximalIdeal R ↔ r b = 0 := fun b => by rw [← hk, RingHom.mem_ker]
  have hO : ∀ o : O, algebraMap O R o ∈ maximalIdeal R → algebraMap O R o ∈ J := fun o ho => by
    rw [hJ]
    refine Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_))
    exact fun hu => ho (hu.map _)
  have hsq : ∀ x ∈ maximalIdeal R, ∀ y ∈ maximalIdeal R, x * y ∈ J := fun x hx y hy => by
    rw [hJ, pow_two]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mul_mem_mul hx hy))
  have hdec : ∀ b : R, ∃ o : O, ∃ x ∈ maximalIdeal R, b = algebraMap O R o + x := fun b => by
    obtain ⟨o, ho⟩ := hs (r b)
    refine ⟨o, b - algebraMap O R o, (hm _).2 ?_, by ring⟩
    rw [map_sub, ← ho]; simp
  let N : Submodule O R := J.restrictScalars O ⊔ 1
  have hNJ : ∀ b ∈ J, N.mkQ b = 0 := fun b hb =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_left hb)
  have hNO : ∀ o : O, N.mkQ (algebraMap O R o) = 0 := fun o =>
    (Submodule.Quotient.mk_eq_zero N).2 (Submodule.mem_sup_right (Submodule.mem_one.2 ⟨o, rfl⟩))
  have hkill : ∀ o : O, r (algebraMap O R o) = 0 → ∀ w : R ⧸ N, o • w = 0 := fun o ho w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [← map_smul, Algebra.smul_def]
    exact hNJ _ (J.mul_mem_right _ (hO o ((hm _).2 ho)))
  letI : SMul F (R ⧸ N) := ⟨fun c w => Function.surjInv hs c • w⟩
  have hsm : ∀ (o : O) (w : R ⧸ N), (r.comp (algebraMap O R)) o • w = o • w := fun o w => by
    show Function.surjInv hs _ • w = o • w
    rw [← sub_eq_zero, ← sub_smul]
    refine hkill _ ?_ w
    have := Function.surjInv_eq hs ((r.comp (algebraMap O R)) o)
    rw [map_sub, map_sub, sub_eq_zero]
    exact this
  letI : Module F (R ⧸ N) := Function.Surjective.moduleLeft (r.comp (algebraMap O R)) hs hsm
  have hder : ∀ b b' : R, N.mkQ (b * b') = r b • N.mkQ b' + r b' • N.mkQ b := fun b b' => by
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    obtain ⟨o', x', hx', rfl⟩ := hdec b'
    have e : (algebraMap O R o + x) * (algebraMap O R o' + x') =
        algebraMap O R (o * o') + (o • x' + o' • x) + x * x' := by
      simp only [Algebra.smul_def, map_mul]; ring
    have e1 : r (algebraMap O R o + x) = (r.comp (algebraMap O R)) o := by
      rw [map_add (f := _), (hm x).1 hx, add_zero]; rfl
    have e2 : r (algebraMap O R o' + x') = (r.comp (algebraMap O R)) o' := by
      rw [map_add (f := _), (hm x').1 hx', add_zero]; rfl
    rw [e, e1, e2, hsm, hsm]
    simp only [map_add (f := _), hNO, hNJ _ (hsq x hx x' hx'), map_smul, zero_add, add_zero]
  have hsurj : ∀ w : R ⧸ N, ∃ b ∈ maximalIdeal R, N.mkQ b = w := fun w => by
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    obtain ⟨o, x, hx, rfl⟩ := hdec b
    exact ⟨x, hx, by rw [map_add (f := _), hNO, zero_add]⟩
  haveI : Module.Finite F (R ⧸ N) := by
    obtain ⟨s, hs'⟩ := IsNoetherian.noetherian (maximalIdeal R)
    refine ⟨Submodule.fg_def.2 ⟨N.mkQ '' s, s.finite_toSet.image _, eq_top_iff.2 fun w _ => ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := hsurj w
    rw [← hs'] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
    | smul c x hx ih =>
      rw [hs'] at hx
      rw [smul_eq_mul, hder, (hm x).1 hx, zero_smul, add_zero]
      exact Submodule.smul_mem _ _ (ih trivial)
  obtain ⟨f1, f2, f3⟩ := dual_of_univ (F := F) N.mkQ.toAddMonoidHom T (fun φ => (hT _).2 ⟨fun b b' => by
      show φ (N.mkQ (b * b')) = r b * φ (N.mkQ b') + r b' * φ (N.mkQ b)
      rw [hder, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul], fun o => by
      show φ (N.mkQ _) = 0
      rw [hNO, map_zero], fun b hb => by
      show φ (N.mkQ _) = 0
      rw [hNJ b (by rw [hJ]; exact Ideal.mem_sup_right hb), map_zero]⟩) (fun α hα => by
    obtain ⟨a1, a2, a3⟩ := (hT α).1 hα
    let K : Ideal R :=
      { carrier := {b | r b = 0 ∧ α b = 0}
        add_mem' := fun {x y} hx hy => ⟨by rw [map_add (f := _), hx.1, hy.1, add_zero], by rw [map_add (f := _), hx.2, hy.2, add_zero]⟩
        zero_mem' := ⟨map_zero _, map_zero _⟩
        smul_mem' := fun c x hx => ⟨by rw [smul_eq_mul, map_mul, hx.1, mul_zero],
          by rw [smul_eq_mul, a1, hx.1, hx.2]; ring⟩ }
    have hK : J ≤ K := by
      rw [hJ]
      refine sup_le (sup_le (Ideal.map_le_iff_le_comap.2 fun o ho => ⟨(hm _).1 (hJm ?_), a2 o⟩) ?_)
        fun b hb => ⟨(hm _).1 (hI hb), a3 b hb⟩
      · rw [hJ]; exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ho))
      · rw [pow_two]
        refine Ideal.mul_le.2 fun x hx y hy => ⟨?_, ?_⟩
        · rw [map_mul, (hm x).1 hx, zero_mul]
        · rw [a1, (hm x).1 hx, (hm y).1 hy]; ring
    have hN : ∀ b ∈ N.toAddSubgroup, α b = 0 := fun b hb => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from hb)
      obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
      rw [map_add (f := _), a2, (hK hy).2, add_zero]
    let ψ : (R ⧸ N) →+ F := QuotientAddGroup.lift N.toAddSubgroup α hN
    have hψ : ∀ b, ψ (N.mkQ b) = α b := fun _ => rfl
    refine ⟨{ toFun := ψ, map_add' := ψ.map_add, map_smul' := fun c w => ?_ }, AddMonoidHom.ext hψ⟩
    obtain ⟨o, rfl⟩ := hs c
    obtain ⟨b, rfl⟩ := N.mkQ_surjective w
    rw [hsm, ← map_smul, hψ, hψ, Algebra.smul_def, a1, a2]
    simp)
  refine ⟨f1, fun b hb h => ?_, fun ξ => ?_⟩
  · have h0 : b ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (f2 b h)
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (show b ∈ J.restrictScalars O ⊔ 1 from h0)
    obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hz
    refine J.add_mem hy (hO o ?_)
    have := (maximalIdeal R).sub_mem hb (hJm hy)
    rwa [add_sub_cancel_left] at this
  · obtain ⟨w, hw⟩ := f3 ξ
    obtain ⟨b, hb, e⟩ := hsurj w
    exact ⟨b, hb, hw b e⟩

theorem UpperTheory.V.Pa.tpDual :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), Module.Finite S.F S.Tp ∧ (∀ b ∈ maximalIdeal S.Bh, (∀ α ∈ S.Tp, α b = 0) → b ∈ S.J2) ∧ ∀ ξ : Module.Dual S.F S.Tp, ∃ b ∈ maximalIdeal S.Bh, ∀ α : S.Tp, (α : S.Bh →+ S.F) b = ξ α := by
  intro l _ S
  haveI : IsNoetherianRing S.Bh := { noetherian := S.d6.noetherian }
  have hI : ired S.U.N ≤ maximalIdeal S.Bh := by
    refine Ideal.span_le.2 ?_
    rintro b ⟨x, hx, y, hy, e⟩
    obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx y hy
    have : b = c := S.U.inj (e.symm.trans e')
    rw [this]
    exact hc
  have hJ : S.J2 ≤ maximalIdeal S.Bh := by
    refine sup_le (sup_le ?_ (Ideal.pow_le_self two_ne_zero)) hI
    exact ((IsLocalRing.local_hom_tfae (algebraMap S.OO S.Bh)).out 1 3).1
      (IsCO.isLocalHom (O := S.OO) (R := S.Bh))
  exact tp_abs S.rF S.rF_ker S.oo_surj (ired S.U.N) S.J2 rfl hI hJ S.Tp fun _ => Iff.rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.invEv :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), l ≠ 2 → ∀ Y : Matrix (Fin n) (Fin n) x.Fr, Y ∈ Ev x.A x.Fr n x.a → Yᵀ = -Y → (∀ g : G.G₀, dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y g = 0) → Y = 0 := by
  intro l hl L G G0 h n x hl2 Y _ hT hd
  have hmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := by
    intro g g'
    simp only [NP.ρX, mat, map_mul, Units.val_mul]
    exact Matrix.map_mul
  have hone : x.ρX x.Fr 1 = 1 := by
    simp only [NP.ρX, mat, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hsurj : Function.Surjective h.p₀ := by
    intro g
    obtain ⟨γ, hγ⟩ := h.surj g.1
    have hm : γ ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, ← h.η γ, hγ]
      exact g.2
    exact ⟨⟨γ, hm⟩, Subtype.ext hγ⟩
  have hc : ∀ g, x.ρX x.Fr g * Y = Y * x.ρX x.Fr g := by
    intro g
    obtain ⟨γ, rfl⟩ := hsurj g
    have e := hd γ
    simp only [dY, sub_eq_zero] at e
    have e2 : x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := by
      rw [← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
    calc x.ρX x.Fr (h.p₀ γ) * Y
        = x.ρX x.Fr (h.p₀ γ) * Y * (x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ)) := by rw [e2, mul_one]
      _ = Y * x.ρX x.Fr (h.p₀ γ) := by rw [← mul_assoc, e]
  have hs : ∀ Z ∈ Submodule.span x.A (mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀)),
      Z.map (algebraMap x.A x.Fr) * Y = Y * Z.map (algebraMap x.A x.Fr) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, _, rfl⟩ := hZ
      exact hc g
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.map_add _ (map_add _), add_mul, mul_add, ha, hb]
    | smul c a _ ha =>
      have : (c • a).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr c • a.map (algebraMap x.A x.Fr) := by
        ext i j; simp
      rw [this, Matrix.smul_mul, Matrix.mul_smul, ha]
  have h2 : (2 : x.Fr) ≠ 0 := by
    have hu : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      have : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hdv
        have : l ∣ 2 := by exact_mod_cast hdv
        exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 this)
      have h3 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)
      simpa using h3
    have := (hu.map (((algebraMap x.A x.Fr).comp (algebraMap x.K x.A)).comp (algebraMap ℤ_[l] x.K))).ne_zero
    rwa [map_ofNat] at this
  ext i j
  by_cases hij : i = j
  · subst hij
    have e := congrFun (congrFun hT i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
    have : (2 : x.Fr) * Y i i = 0 := by linear_combination e
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · have hE : (Matrix.single i i (1 : x.A)) ∈ Ev x.A x.A n x.a := by
      intro p q
      refine ⟨fun _ => trivial, fun hne => ?_⟩
      rw [Submodule.mem_bot]
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact hne Iff.rfl
    obtain ⟨s, hsp⟩ := x.span _ hE
    have e := hs _ hsp
    have hm : ((PowerSeries.X : PowerSeries x.K) ^ s • Matrix.single i i (1 : x.A)).map (algebraMap x.A x.Fr)
        = Matrix.single i i (algebraMap x.A x.Fr (x.t ^ s)) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_single]
    rw [hm] at e
    have e' := congrFun (congrFun e i) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij)] at e'
    have ht : algebraMap x.A x.Fr (x.t ^ s) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    simpa using (mul_eq_zero.1 e').resolve_left ht
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.indF :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ c : Fin k.g → x.Fr, ∑ j, c j • kapF h k j ∈ BdM h x x.Fr → c = 0 := by
  intro l _ L G G0 h n x k c hc
  classical
  obtain ⟨Y, hY, hYt, hcY⟩ := hc
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have hsurj : Function.Surjective h.p₀ := by
    rintro ⟨g', hg'⟩
    obtain ⟨γ, hγ⟩ := h.surj g'
    refine ⟨⟨γ, ?_⟩, Subtype.ext hγ⟩
    show G.η γ = 1
    rw [← h.η, hγ]
    exact hg'
  have hb : ∃ b : nonZeroDivisors x.A, ∀ i : Fin k.g ⊕ (Fin n × Fin n),
      ∃ r : x.A, algebraMap x.A x.Fr r = (b : x.A) • Sum.elim c (fun p => Y p.1 p.2) i :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors x.A) _
  obtain ⟨b, hb⟩ := hb
  choose a ha using hb
  let cA : Fin k.g → x.A := fun j => a (Sum.inl j)
  let YA : Matrix (Fin n) (Fin n) x.A := fun i j => a (Sum.inr (i, j))
  let ψ := (Algebra.ofId x.A x.Fr).mapMatrix (m := Fin n)
  have hψ : ∀ M : Matrix (Fin n) (Fin n) x.A, ψ M = M.map (algebraMap x.A x.Fr) := fun M => rfl
  have hψinj : Function.Injective ψ := by
    intro M N hMN
    refine Matrix.ext fun i j => ?_
    apply hinj
    have := congrFun (congrFun hMN i) j
    rwa [hψ, hψ] at this
  have hψY : ψ YA = (b : x.A) • Y := by
    refine Matrix.ext fun i j => ?_
    rw [hψ]
    exact ha (Sum.inr (i, j))
  have hρ : ∀ g, ψ (x.ρX x.A g) = x.ρX x.Fr g := by
    intro g
    refine Matrix.ext fun i j => ?_
    simp [hψ, NP.ρX]
  have hκ : ∀ j γ, ψ (k.κ j (h.p₀ γ)) = kapF h k j γ := fun j γ => rfl
  have hcj : ∀ j (M : Matrix (Fin n) (Fin n) x.Fr), cA j • M = (b : x.A) • (c j • M) := by
    intro j M
    rw [← algebraMap_smul x.Fr (cA j) M, ha (Sum.inl j), Sum.elim_inl, smul_assoc]
  have hmem : ∑ j, cA j • k.κ j ∈ Bd G0.frame (x.ρX x.A) (Od x.A x.A n x.a) := by
    refine ⟨YA, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
      have h0 : Y i j = 0 := (Submodule.mem_bot _).1 ((hY i j).1 hij)
      rw [Submodule.mem_bot]
      apply hinj
      rw [map_zero]
      have := ha (Sum.inr (i, j))
      rw [Sum.elim_inr, h0, smul_zero] at this
      exact this
    · refine Matrix.ext fun i j => ?_
      apply hinj
      have h1 := ha (Sum.inr (j, i))
      have h2 := ha (Sum.inr (i, j))
      rw [Sum.elim_inr] at h1 h2
      have hYij : Y j i = - Y i j := congrFun (congrFun hYt i) j
      rw [Matrix.transpose_apply, Matrix.neg_apply, map_neg]
      show algebraMap x.A x.Fr (a (Sum.inr (j, i))) = -algebraMap x.A x.Fr (a (Sum.inr (i, j)))
      rw [h1, h2, hYij, smul_neg]
    · funext g'
      obtain ⟨γ, rfl⟩ := hsurj g'
      apply hψinj
      have hL : ψ ((∑ j, cA j • k.κ j) (h.p₀ γ)) = (b : x.A) • (∑ j, c j • kapF h k j) γ := by

        simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hκ, hcj, Finset.smul_sum]
      rw [hL, hcY]
      simp only [dY, map_sub, map_mul, hρ, hψY, Matrix.mul_smul, Matrix.smul_mul, smul_sub, map_inv]
  have hzero := k.indep cA hmem
  funext j
  have hj := ha (Sum.inl j)
  have h0 : cA j = 0 := congrFun hzero j
  rw [Sum.elim_inl, Algebra.smul_def] at hj
  change algebraMap x.A x.Fr (cA j) = _ at hj
  rw [h0, map_zero] at hj
  have hb0 : algebraMap x.A x.Fr (b : x.A) ≠ 0 := fun h0' =>
    nonZeroDivisors.ne_zero b.2 (hinj (h0'.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hj.symm).resolve_left hb0
end
