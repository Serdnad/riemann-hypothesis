module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Mathlib.Algebra.Field.ZMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle014
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle005
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

private theorem le_ker [IsTopologicalGroup Γ] {G : Type} [Monoid G] (φ : Γ →* G) (h : IsLocallyConstant φ)
    (N : Set Γ) (hN : ∀ g ∈ N, φ g = 1) : (Subgroup.normalClosure N).topologicalClosure ≤ φ.ker := by
  have hc : IsClosed (φ.ker : Set Γ) := by
    have : (φ.ker : Set Γ) = {g | φ g = 1} := rfl
    rw [this]
    exact (h.isClopen_fiber 1).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

private theorem lc_quot {Y : Type} (M : Subgroup Γ) (f : Γ ⧸ M → Y)
    (h : IsLocallyConstant fun g : Γ => f (QuotientGroup.mk g)) : IsLocallyConstant f := fun s =>
  (QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)

private theorem phi_quot (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → M ≤ H →
      Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ M → φ g = 1}) :
    PhiCond (Γ := Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc) fun g hg => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact H.one_mem
  let π := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective π :=
    (QuotientGroup.mk' M).subgroupComap_surjective_of_surjective H (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
      IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M))) ∧
        ∀ g : H.comap (QuotientGroup.mk' M), (g : Γ) ∈ M → φ g = 1})
    (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ, fun g hg => ?_⟩) fun φ φ' e => ?_
  · have : π g = 1 := Subtype.ext ((QuotientGroup.eq_one_iff (g : Γ)).2 hg)
    rw [MonoidHom.comp_apply, this, map_one]
  · exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
  {rbar : Γ →* Matrix ι ι (ResidueField Λ)}

private theorem kills_closure [IsTopologicalGroup Γ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    (s : Lift Λ rbar R) (N : Set Γ) (hN : ∀ g ∈ N, s.hom g = 1) :
    (Subgroup.normalClosure N).topologicalClosure ≤ s.hom.ker := by
  have key : ∀ x y : R, (∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) x = Ideal.Quotient.mk _ y) → x = y := by
    intro x y hxy
    have hH : IsHausdorff (maximalIdeal R) R := (IsCO.complete (O := Λ)).toIsHausdorff
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 (hxy n)
  have hc : IsClosed (s.hom.ker : Set Γ) := by
    have : (s.hom.ker : Set Γ) = ⋂ a, ⋂ b, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (maximalIdeal R ^ n) (s.hom g a b) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) ((1 : Matrix ι ι R) a b)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hg a b n
        rw [hg]
      · intro hg
        ext a b
        exact key _ _ (hg a b)
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun n =>
      ((s.cont a b n).isClopen_fiber _).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

end

theorem UpperTheory.V.Ws.sxUnivKill :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField Λ)) (N : Set Γ), (∀ H : Subgroup Γ, IsOpen (H : Set Γ) → Subgroup.normalClosure N ≤ H → Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ (Subgroup.normalClosure N).topologicalClosure → φ g = 1}) → IsLocallyConstant rbar → (∀ n ∈ N, rbar n = 1) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ rbar R), Represents (killCond rbar N) r := by
  intro l _ Λ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ _ rbar N hfin hloc hN
  haveI : (Subgroup.normalClosure N).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hKc : IsClosed ((Subgroup.normalClosure N).topologicalClosure : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  haveI : TotallyDisconnectedSpace (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) :=
    (UpperTheory.V.AlgebraTools.totallyDisconnected_quot Γ _ hKc).1
  have hK : (Subgroup.normalClosure N).topologicalClosure ≤ rbar.ker := le_ker rbar hloc N hN
  let rq : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure →* Matrix ι ι (ResidueField Λ) :=
    QuotientGroup.lift _ rbar hK
  have hlq : IsLocallyConstant rq := lc_quot _ rq hloc
  have hΦ : PhiCond (Γ := Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) l :=
    phi_quot l _ fun H hH hKH => hfin H hH (le_trans (Subgroup.le_topologicalClosure _) hKH)
  obtain ⟨R, _, _, _, r0, hr0⟩ := univ_lift l Λ (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) ι rq hΦ hlq
  let r : Lift Λ rbar R :=
    ⟨r0.hom.comp (QuotientGroup.mk' _), fun a b n => (r0.cont a b n).comp_continuous continuous_quot_mk,
      fun g a b => r0.red (g : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, r, ?_⟩
  intro R' _ _ _
  constructor
  · intro f n hn
    have h1 : ((n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure)) = 1 :=
      (QuotientGroup.eq_one_iff n).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hn))
    ext a b
    rw [Lift.map_hom]
    show f (r0.hom (n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) = _
    rw [h1, map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro r' hr'
    have hK' : (Subgroup.normalClosure N).topologicalClosure ≤ r'.hom.ker := kills_closure r' N hr'
    let rq' : Lift Λ rq R' :=
      ⟨QuotientGroup.lift _ r'.hom hK', fun a b n => lc_quot _ _ (r'.cont a b n), fun q a b => by
        induction q using QuotientGroup.induction_on with
        | H g => exact r'.red g a b⟩
    obtain ⟨f, hf, huniq⟩ := (hr0 R').2 rq' trivial
    have key : ∀ g : R →ₐ[Λ] R', Lift.map g r = r' ↔ Lift.map g r0 = rq' := by
      intro g
      constructor
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          ext a b
          have := congrArg (fun y : Lift Λ rbar R' => y.hom x a b) h
          exact (Lift.map_hom g r0 _ a b).trans ((Lift.map_hom g r x a b).symm.trans this)
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun x => ?_
        ext a b
        have := congrArg (fun y : Lift Λ rq R' => y.hom (x : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) h
        exact (Lift.map_hom g r x a b).trans ((Lift.map_hom g r0 _ a b).symm.trans this)
    exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtA :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.A →ₐ[Λ] R'), (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz R' _ _ _ f f' hf
  haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ X R W hz
  let ι : ↥(W.gr 0) →ₐ[Λ] W.A :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  have hzA : ∀ s, ((W.zA s : W.A) : R) = W.z s := fun _ => rfl
  have h0 : f.comp ι = f'.comp ι := by
    refine sxExtGr0 W hz R' _ _ ?_
    intro b n _ hb
    have hbA : (b : W.A) = n.prod fun s k => W.zA s ^ k := by
      apply Subtype.ext
      rw [hb]
      simp [Finsupp.prod, hzA]
    show f (b : W.A) = f' (b : W.A)
    rw [hbA]
    simp [Finsupp.prod, map_prod, map_pow, hf]
  refine AlgHom.ext_of_adjoin_eq_top (gr_gen Λ R X W) ?_
  rintro x (hx | ⟨s, rfl⟩)
  · exact congrArg (fun g => g ⟨x, hx⟩) h0
  · exact hf s
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* R) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => ψ g
  map_one' := Matrix.ext fun _ _ => by simp
  map_mul' g h := Matrix.ext fun _ _ => by simp [Matrix.mul_apply]

private def ofMat {G R : Type} [Group G] [CommRing R] (r : G →* Matrix Unit Unit R) : G →* R where
  toFun g := r g () ()
  map_one' := by simp
  map_mul' g h := by simp [Matrix.mul_apply]

theorem UpperTheory.V.Ws.sxUnivChar :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : G →* ResidueField Λ), PhiCond (Γ := G) l → IsLocallyConstant χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (ψ : G →* R), AdicCont (maximalIdeal R) ψ ∧ (∀ s, res Λ R (ψ s) = χ s) ∧ ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (ψ' : G →* R'), AdicCont (maximalIdeal R') ψ' → (∀ s, res Λ R' (ψ' s) = χ s) → ∃! f : R →ₐ[Λ] R', ∀ s, f (ψ s) = ψ' s := by
  intro l _ Λ _ _ _ _ _ _ G _ _ _ _ _ χ hΦ hχ
  have hloc : IsLocallyConstant (toMat χ) :=
    hχ.comp (fun x : ResidueField Λ => (Matrix.of fun _ _ => x : Matrix Unit Unit (ResidueField Λ)))
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l Λ G Unit (toMat χ) hΦ hloc
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat r.hom, r.cont () (), fun s => r.red s () (), ?_⟩
  intro R' _ _ _ ψ' hc hred
  let r' : Lift Λ (toMat χ) R' := ⟨toMat ψ', fun _ _ => hc, fun g _ _ => hred g⟩
  obtain ⟨f, hf, huniq⟩ := (hr R').2 r' trivial
  have key : ∀ g : R →ₐ[Λ] R', (∀ s, g (ofMat r.hom s) = ψ' s) ↔ Lift.map g r = r' := by
    intro g
    constructor
    · intro h
      apply Lift.ext
      ext s a b
      cases a
      cases b
      exact (Lift.map_hom g r s () ()).trans (h s)
    · intro h s
      have := congrArg (fun x : Lift Λ (toMat χ) R' => x.hom s () ()) h
      exact (Lift.map_hom g r s () ()).symm.trans this
  exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearArt :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), IsNilpotent (maximalIdeal R') → Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hnil hQ
  have hc : ∀ i j, -((∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs : ℕ) : ℤ) ≤ τ (wt i j) := by
    intro i j
    have h1 : (τ (wt i j)).natAbs ≤ ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs :=
      Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
    omega
  generalize (∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs) = c at hc
  obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
  obtain ⟨Q', hQ', hr, hψ⟩ := sxScaleRD hnil he hc hQ
  obtain ⟨F, hF, -⟩ := hU.2 S Q' hQ'
  have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (Q.r g i j) := by
    intro g i j
    rw [← hr, ← hF]; rfl
  have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (Q.ψ v i s) := by
    intro v i s
    rw [← hψ, ← hF]; rfl
  have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
    intro s
    rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
    · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
      by_cases hij : i = j
      · rw [(wt_eq_zero i j).2 hij, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
      · rw [h3 hij]
        exact ⟨Q.r g i j, by simp⟩
    · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
      exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
  obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
  have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
    intro g i j
    rw [← hD']; rfl
  have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']; rfl
  refine ⟨f, RD.ext ?_ ?_⟩
  · ext g i j
    have hm : D'.r g i j ∈ W.gr (wt i j) := by
      show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
      rw [er]; exact hG.ent g i j
    have h := hf _ _ hm
    rw [er, hFr] at h
    exact (HahnSeries.single_injective _ h).symm
  · funext v i
    ext s
    have hm : D'.ψ v i s ∈ W.gr 0 := by
      show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
      rw [eψ]; exact hG.chr v i s
    have h := hf _ _ hm
    rw [eψ, hFψ, map_zero] at h
    exact (HahnSeries.single_injective _ h).symm
end
