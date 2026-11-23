module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.LevEps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f)
    (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

private theorem ac_map {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [CommRing R] {J : Ideal O} {I : Ideal R} (φ : O →+* R)
    (h : ∀ a ∈ J, φ a ∈ I) {f : Γ → O} (hf : AdicCont J f) : AdicCont I fun x => φ (f x) := by
  intro N
  have hJ : Ideal.map φ J ≤ I := Ideal.map_le_iff_le_comap.mpr (fun a ha => h a ha)
  have hN : J ^ N ≤ Ideal.comap φ (I ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hJ N
  have := (hf N).comp (Ideal.Quotient.lift (J ^ N) ((Ideal.Quotient.mk (I ^ N)).comp φ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext x
  rfl

private theorem ac_closed {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} [IsHausdorff I R] {f : Γ → R}
    (hf : AdicCont I f) (y : R) : IsClosed {x | f x = y} := by
  have hset : {x | f x = y} =
      ⋂ N : ℕ, {x | Ideal.Quotient.mk (I ^ N) (f x) = Ideal.Quotient.mk (I ^ N) y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro hx N
      rw [hx]
    · intro hx
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro N
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using Ideal.Quotient.eq.mp (hx N)
  rw [hset]
  exact isClosed_iInter fun N => ((hf N).isClopen_fiber _).isClosed

theorem UpperTheory.V.Ws.P1.rhoEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (I : Ideal R) [IsHausdorff I R], (∀ a ∈ maximalIdeal c'.O, algebraMap c'.O R a ∈ I) → (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → Q.Cont I →
          ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) R, K.IsRho ρ Q ∧ ∀ a b, AdicCont I fun g => W.mat ρ g a b := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q I _ hI hpair hcont
  let σ : G T.L Ω →* M4 R :=
    { toFun := fun g => algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }
  let ρ' : G T.L Ω →* GL (Fin 4) R := σ.toHomUnits
  have hρ' : ∀ g, ((ρ' g : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g := fun g => rfl
  have hent : ∀ a b, AdicCont I fun g => σ g a b := by
    intro a b
    have h1 : AdicCont I fun g : G T.L Ω => algebraMap c'.O R (K.κ g : c'.O) :=
      ac_map (algebraMap c'.O R) hI K.κ_cont
    have h2 : AdicCont I fun g : G T.L Ω => Q.r (resLe T.F_le g) a b := by
      intro N
      exact (hcont a b N).comp_continuous (P1.towerGal D T).2.2.1
    exact ac_mul h1 h2
  have hker : K.V.pr.ker ≤ ρ'.ker := by
    apply (phiKer K.V).2.2 ρ'.ker
    · have hset : (ρ'.ker : Set (G T.L Ω)) =
          ⋂ a, ⋂ b, {g | σ g a b = (1 : Matrix (Fin 4) (Fin 4) R) a b} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
        rw [← Units.val_eq_one, hρ']
        exact ⟨fun hg a b => by rw [hg], fun hg => Matrix.ext hg⟩
      rw [hset]
      exact isClosed_iInter fun a => isClosed_iInter fun b => ac_closed (hent a b) _
    · intro A v hAv hv g hg
      rw [K.hV] at hv
      obtain ⟨hκ, hr⟩ := K.unr A v hAv hv g hg
      have hl : ¬ A.valuation (l : Ω) < 1 := by
        intro hlt
        apply hv
        left
        have hmem := (hAv (l : 𝓞 (W.Lp T.L))).mp (by simpa using hlt)
        simpa using hmem
      have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
        change ∃ A', Raw.Away (insert l ∅) A' ∧ resLe T.F_le g ∈ Ine A' ∧
          D.rbar ((resQ T.F) (resLe T.F_le g)) = 1
        refine ⟨A, ?_, ((P1.towerGal D T).2.2.2.2.2 A g).2.mpr hg, ?_⟩
        · intro p hp
          simp at hp
          subst hp
          exact hl
        · rw [((P1.towerGal D T).2.2.2.2.1 g).1]
          exact hr
      rw [MonoidHom.mem_ker, ← Units.val_eq_one, hρ']
      show algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g) = 1
      rw [hκ, hpair.kill _ hN]
      simp
  let e := QuotientGroup.quotientKerEquivOfSurjective K.V.pr (phiKer K.V).1
  let ρ : K.V.frame.G₀ →* GL (Fin 4) R :=
    (QuotientGroup.lift K.V.pr.ker ρ' hker).comp e.symm.toMonoidHom
  have hρ : ∀ g, ρ (K.V.pr g) = ρ' g := by
    intro g
    have he : e.symm (K.V.pr g) = (g : G T.L Ω ⧸ K.V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift K.V.pr.ker ρ' hker (e.symm (K.V.pr g)) = ρ' g
    rw [he]
    rfl
  have hmat : ∀ g, W.mat ρ (K.V.pr g) = σ g := by
    intro g
    show ((ρ (K.V.pr g) : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g
    rw [hρ, hρ']
  refine ⟨ρ, fun g => ?_, fun a b => ?_⟩
  · rw [hmat]
    rfl
  · intro N
    have hq := (phiKer K.V).2.1
    have heq : (fun x => Ideal.Quotient.mk (I ^ N) (W.mat ρ x a b)) ∘ K.V.pr =
        fun g => Ideal.Quotient.mk (I ^ N) (σ g a b) := by
      funext g
      show Ideal.Quotient.mk (I ^ N) (W.mat ρ (K.V.pr g) a b) = _
      rw [hmat]
    intro s
    have hopen := hent a b N s
    rw [← heq] at hopen
    exact hq.isOpen_preimage.mp hopen
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem res_one_lemma {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (f : A →+* B) (y : A) (hy : IsLocalRing.residue B (f y) = 1) : IsLocalRing.residue A y = 1 := by
  change Ideal.Quotient.mk _ (f y) = Ideal.Quotient.mk _ 1 at hy
  change Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ 1
  rw [Ideal.Quotient.eq] at hy ⊢
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
  intro hu
  apply hy
  simpa using hu.map f

theorem UpperTheory.V.Ws.P1.ineTriv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q → ∀ u, ∀ g ∈ K.r.Ip u, ρ g = 1 := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ u g hg
  simp only [W.Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hg
  obtain ⟨hgu, hgc⟩ := hg
  unfold UpperTheory.V.W.HidaSetting.Lev.frame at hgu u
  obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hgu
  have hu : (u : W.Plc (W.Lp ↥T.L)) ∈ K.s.St := u.2
  have hsurj : ∀ b : Bool, ∀ j : Fin 4, ∃ i, lab b i = j := by decide
  have key : ∀ i, IsLocalRing.residue c'.O
      ((K.κ g' : c'.O) * inc h (D.ps (lab T.pr i) (resQ T.L g') : c.O)) = 1 := by
    intro i
    have e := K.chib i g'
    rw [hgc i, Units.val_one] at e
    exact e.symm
  have hκr : IsLocalRing.residue c'.O (K.κ g' : c'.O) = 1 := by
    obtain ⟨i, hi⟩ := hsurj T.pr 3
    have e := key i
    rw [hi] at e
    simpa [Raw.ps] using e
  have hres : ∀ j, IsLocalRing.residue c.O (D.ps j (resQ T.L g') : c.O) = 1 := by
    intro j
    obtain ⟨i, hi⟩ := hsurj T.pr j
    have e := key i
    rw [hi, map_mul, hκr, one_mul] at e
    exact res_one_lemma (inc h) _ e
  have hrb : D.rbar (resQ T.L g') = 1 := by
    have hf : (fun i => IsLocalRing.residue c.O (D.ps i (resQ T.L g') : c.O)) = fun _ => 1 := funext hres
    show (RingHom.mapMatrix (IsLocalRing.residue c.O))
      (Matrix.diagonal fun i => (D.ps i (resQ T.L g') : c.O)) = 1
    rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), hf, Matrix.diagonal_one]
  have hnl : ¬ (K.s.A ↑u).valuation (l : Ω) < 1 := by
    intro hlt
    have hin := (K.s.hA ↑u (l : 𝓞 (W.Lp ↥T.L))).mp (by simpa using hlt)
    exact K.s.St_l ↑u hu (by simpa using hin)
  obtain ⟨m, hm, hκt⟩ := K.tame
  have hκm := hκt (K.s.A ↑u) hnl g' hg'
  have hκ1 : (K.κ g' : c'.O) = 1 :=
    (coefRes c').2.2.2 m _ hm (by rw [← Units.val_pow_eq_pow_val, hκm, Units.val_one]) hκr
  have hQr : Q.r (resLe T.F_le g') = 1 := by
    apply hQ.kill
    unfold UpperTheory.V.Ws.Tower.fr
    simp only [Set.mem_setOf_eq]
    refine ⟨K.s.A ↑u, ?_, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hp
      subst hp
      exact hnl
    · exact ((towerGal D T).2.2.2.2.2 _ g').2.mpr hg'
    · rw [((towerGal D T).2.2.2.2.1 g').1]
      exact hrb
  have e := hρ g'
  rw [hQr, hκ1, map_one, one_smul] at e
  exact Units.ext e
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.condA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ), K.IsPsi ψ Q → (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, Q.ψ v i s ≠ Q.ψ v j s) →
          Nonempty K.V.frame.Vl ∧ ∀ v i j, i ≠ j → ∃ g, K.V.frame.φ v g ∈ K.V.frame.G' ∧ K.r.psib v i g = K.r.psib v j g ∧ ψ v i g ≠ ψ v j g := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K R _ _ Q ψ hψ hsep
  obtain ⟨hrange, -, -, -, hres, hloc⟩ := P1.towerGal D T
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hlev := P1.levEps K.V
  refine ⟨hlev.2.2.1, fun v i j hij => ?_⟩
  obtain ⟨s, ⟨hsI, hscyc, hsr⟩, hne⟩ := hsep (K.e v) i j hij
  have hsL : s ∈ T.GalL := hfit.1.unr _ hsI
  rw [← hrange] at hsL
  obtain ⟨g', rfl⟩ := hsL
  have hgD : g' ∈ (Dec (K.s.A (show W.Vl l T.L from v).1) : Subgroup (G T.L Ω)) := by
    rw [K.hA v]
    exact Ine_le_Dec _ (((hloc _ g').2).1 hsI)
  have hr : D.rbar (resQ T.L g') = 1 := by rw [← (hres g').1]; exact hsr
  have hk : ∀ k, residue c'.O (inc h ↑(chi D T.pr k (resQ T.L g'))) = 1 := by
    intro k
    have e := congrArg (fun M => M (lab T.pr k) (lab T.pr k)) hr
    simp [Raw.rbar, Raw.r0, mapRep, diagRep] at e
    rw [← ResidueField.map_residue]
    simp [chi, e]
  refine ⟨⟨g', hgD⟩, ?_, ?_, ?_⟩
  · show K.V.pr g' ∈ K.V.frame.G'
    rw [(hlev.2.1 g'), ← (hres g').2.1]
    exact hscyc
  · have hc : K.r.chib i (K.V.pr g') = K.r.chib j (K.V.pr g') := by
      apply Units.ext
      rw [K.chib, K.chib, map_mul, map_mul, hk, hk]
    exact (K.psib v i ⟨g', hgD⟩).trans (hc.trans (K.psib v j ⟨g', hgD⟩).symm)
  · intro heq
    apply hne
    have e1 := hψ v i ⟨g', hgD⟩
    have e2 := hψ v j ⟨g', hgD⟩
    rw [heq] at e1
    have hu : IsUnit (algebraMap c'.O R ↑(K.κ g')) := (K.κ g').isUnit.map _
    exact hu.mul_left_cancel (e1.symm.trans e2)
end
