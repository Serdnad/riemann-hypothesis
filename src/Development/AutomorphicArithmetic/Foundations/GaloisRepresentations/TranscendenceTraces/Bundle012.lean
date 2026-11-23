module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle043
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
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def toOf {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) : A.To (Sq.of p A.u) :=
  ⟨𝟙 _, pullback.lift A.v A.r A.pb.w, Category.id_comp _, pullback.lift_fst _ _ _,
    (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩

private noncomputable def ofTo {Z S V U : Scheme.{0}} (p : Z ⟶ S) (g : V ⟶ U) (u : U ⟶ S) :
    (Sq.of p (g ≫ u)).To (Sq.of p u) :=
  ⟨g, pullback.lift (pullback.fst p (g ≫ u)) (pullback.snd p (g ≫ u) ≫ g)
      (pullback.condition.trans (Category.assoc _ _ _).symm),
    rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private noncomputable def imgVal {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s)
    (U : Scheme.{0}) (u : U ⟶ S) : Sec (J.X s) U :=
  (τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imgBasic_of :
    ImgBasic := by
  intro Z S p R' R _ _ I J τ n
  have ev_def {T : Type} [CommRing T] {E : Spc} {K : Cx T} {j : ℤ}
      (α : Cochain ((chains T).obj E) K j) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx E k U) : ev (R := T) α k s h U x =
        Sec.map ((chainsXIso T E k).inv ≫ α.v _ _ h) (freeGen T _ U x) := rfl
  refine ⟨fun α => ?_, fun m hm α β hαβ => ?_⟩
  · have ev_res (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) {V U : Scheme.{0}}
        (g : V ⟶ U) (x : Sx (sch.obj Z) k U) :
        Sec.res g (ev (R := R') α k s h U x) = ev (R := R') α k s h V (Sx.res g x) := by
      rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
      rfl
    have ev_ext (β' β : Cochain ((chains R).obj (sch.obj S)) J n)
        (he : ∀ k s h U x, ev (R := R) β' k s h U x = ev (R := R) β k s h U x) : β' = β := by
      ext i s hs : 1
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        rw [← cancel_epi (chainsXIso R (sch.obj S) k).inv]
        exact CupSpec.free_ext _ _ (fun U x => he k s hs U x)
      · exact (CupSpec.isZero_chains (sch.obj S) i (by omega)).eq_of_src _ _
    have hnat : ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (V U : Scheme) (g : V ⟶ U) (u : Sx (sch.obj S) k U),
        Sec.res g (imgVal τ α k s h U u) = imgVal τ α k s h V (Sx.res g u) := by
      intro k s h V U g u
      have e1 : Sec.res g ((τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) =
          (τ.deg s).app (Sq.of p (g ≫ u)) (Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) :=
        (τ.deg s).nat (ofTo p g u) _
      have e2 : Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u)) =
          ev (R := R') α k s h (pullback p (g ≫ u)) (pullback.fst p (g ≫ u)) := by
        refine (ev_res k s h (ofTo p g u).k (pullback.fst p u)).trans ?_
        congr 1
        show (ofTo p g u).k ≫ pullback.fst p u = pullback.fst p (g ≫ u)
        exact pullback.lift_fst _ _ _
      exact e1.trans (congrArg _ e2)
    have hex := exists_cochain_ev_eq_of_natural R (E := sch.obj S) (I := J) (n := n)
      (imgVal τ α) hnat
    obtain ⟨β, hβ⟩ := hex
    have hIm : τ.IsImage α β := by
      intro k s h A
      have e1 : Sec.res (toOf A).g ((τ.deg s).app (Sq.of p A.u) (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) =
          (τ.deg s).app A (Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) :=
        (τ.deg s).nat (toOf A) _
      have e2 : Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u)) =
          ev (R := R') α k s h A.V A.v := by
        refine (ev_res k s h (toOf A).k (pullback.fst p A.u)).trans ?_
        congr 1
        show (toOf A).k ≫ pullback.fst p A.u = A.v
        exact pullback.lift_fst _ _ _
      exact (hβ k s h A.U A.u).trans (((res_id _).symm.trans e1).trans (congrArg _ e2))
    refine ⟨β, hIm, fun β' h' => ev_ext β' β (fun k s h U u => ?_)⟩
    exact (h' k s h (Sq.of p u)).trans (hIm k s h (Sq.of p u)).symm
  · have ev_delta_zero {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (x : Sx E 0 U) :
        ev (R := T) (δ n m γ) 0 m (by simp) U x =
          Sec.map (K.d n m) (ev (R := T) γ 0 n (by simp) U x) := by
      rw [ev_def, δ_v n m hm γ _ m (by simp) n 1 (by omega) (by simp),
        (CupSpec.isZero_chains E 1 one_pos).eq_of_tgt (((chains T).obj E).d _ 1) 0,
        zero_comp, smul_zero, add_zero]
      rfl
    have ev_delta_succ {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (q : ℕ) (s t : ℤ)
        (hs : -((q + 1 : ℕ) : ℤ) + n = s) (ht : -((q + 1 : ℕ) : ℤ) + m = t)
        (x : Sx E (q + 1) U) :
        ev (R := T) (δ n m γ) (q + 1) t ht U x =
          Sec.map (K.d s t) (ev (R := T) γ (q + 1) s hs U x) +
            m.negOnePow • ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
              ev (R := T) γ q t (by omega) U (x.face i) := by
      rw [ev_def, δ_v n m hm γ _ t ht s (-(q : ℤ)) (by omega) (by omega), Preadditive.comp_add,
        Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains T).obj E).d _ _),
        CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen T _ U x)) _ _).trans ?_

      rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso T E q).inv ≫ γ.v _ _ _)
        (Sec.map ((free T).map _) (freeGen T _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    intro k s h A
    cases k with
    | zero =>
      have hs : s = m := by simpa using h.symm
      subst hs
      have eβ := ev_delta_zero (E := sch.obj S) β A.U A.u
      have eα := ev_delta_zero (E := sch.obj Z) α A.V A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      refine (congrArg _ (hαβ 0 n (by simp) A)).trans ?_
      exact τ.comm A n s _
    | succ q =>
      have eβ := ev_delta_succ (E := sch.obj S) β A.U q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.u
      have eα := ev_delta_succ (E := sch.obj Z) α A.V q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      rw [map_add (f := _)]
      congr 1
      · exact (congrArg _ (hαβ _ _ rfl A)).trans (τ.comm A _ s _)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        exact hαβ q s _ A
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.coverOne_of :
    CoverOne := by
  intro R _ F G f V b h
  have hd : ∀ (V' W : Scheme.{0}) (g : V' ⟶ V) (k : W ⟶ V'),
      (∃ a : Sec F V', Sec.map f a = Sec.res g b) → ∃ a : Sec F W, Sec.map f a = Sec.res (k ≫ g) b := by
    rintro V' W g k ⟨a, ha⟩
    exact ⟨Sec.res k a, by rw [map_res, ha, res_res]⟩
  have h2 := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V (fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) hd).1 h
  choose Wf k _ het hx a ha using h2
  obtain ⟨a', ha'⟩ := (GlobalTheory.T.sec_sigma_res_bijective R F Wf).2 a
  refine ⟨∐ Wf, Sigma.desc k, a', ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => het i
  · refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := hx x
    refine ⟨Sigma.ι Wf x y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]
  · refine (GlobalTheory.T.sec_sigma_res_bijective R G Wf).1 (funext fun i => ?_)
    show Sec.res (Sigma.ι Wf i) (Sec.map f a') = Sec.res (Sigma.ι Wf i) (Sec.res (Sigma.desc k) b)
    have e : Sec.res (Sigma.ι Wf i) a' = a i := congrFun ha' i
    rw [← map_res, e, ha, res_res, Sigma.ι_desc]
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sHSec_of :
    SHSec := by
  intro T C _ _ _ _ _ hSH
  obtain ⟨hH, hS⟩ := hSH
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := C)
    (⟨IsLocalRing.maximalIdeal T, inferInstance⟩ : PrimeSpectrum T)
  have hq' : (PrimeSpectrum.asIdeal q).comap (algebraMap T C) = IsLocalRing.maximalIdeal T :=
    congrArg PrimeSpectrum.asIdeal hq
  haveI : (PrimeSpectrum.asIdeal q).IsPrime := PrimeSpectrum.isPrime q
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff T).2 ⟨inferInstance, inferInstance⟩
    C (PrimeSpectrum.asIdeal q) hq'
  exact ⟨s⟩
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : p.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _
  haveI : IsPurelyInseparable L (AlgebraicClosure L) :=
    IsPurelyInseparable.tower_top K L (AlgebraicClosure L)
  have hs : IsSeparable L r := Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)
  obtain ⟨x, rfl⟩ := IsPurelyInseparable.inseparable' r hs
  refine ⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨hH, hS⟩ := hO
  haveI := hH
  haveI := hT
  refine ⟨hT, ?_⟩
  haveI : IsLocalHom (algebraMap O T) := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal O := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)] at h1
    exact (Ideal.mem_comap.1 h1) ha⟩
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨p, hp, h0⟩ := Algebra.IsIntegral.isIntegral (R := O) t
    refine IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp
        (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T) := rfl
    rw [h2, ← Polynomial.hom_eval₂, h0, map_zero]
  exact sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _

private theorem exists_ringHom (hS : SHSec) (B C T : Type) [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra.Etale B C] [Module.FaithfullyFlat B C] [Algebra B T] (hT : SH T) :
    ∃ f : C →+* T, ∀ b, f (algebraMap B C b) = algebraMap B T b := by
  obtain ⟨s⟩ := hS T (T ⊗[B] C) hT
  refine ⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩
  have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) =
      algebraMap T (T ⊗[B] C) (algebraMap B T b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]
  change s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _
  rw [h1]
  exact s.commutes _

end UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

open UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable in
theorem UpperTheory.Gal.TranscendenceTraces.finSec_of :
    SHSec → FinSec := by
  intro hS O B C _ _ _ _ _ _ _ _ hO
  obtain ⟨hH, -⟩ := id hO
  haveI := hH
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B
  have key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i := by
    intro i
    haveI := (hT i).2
    have hs := sh_of_finite O (T i) hO (hT i).1
    letI : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra
    exact exists_ringHom hS B C (T i) hs
  choose f hf using key
  refine ⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (Pi.ringHom f), commutes' := fun b => ?_ }⟩
  have h : Pi.ringHom f (algebraMap B C b) = e b := funext fun i => hf i b
  change e.symm (Pi.ringHom f (algebraMap B C b)) = b
  rw [h]
  exact e.symm_apply_apply b
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private theorem root_orbit {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (b : B) : ∃ g : G, ψ b = φ (g • b) :=
  _root_.UpperTheory.Reformulated.B.Qi49.root_orbit φ ψ h b

private theorem same_ker {A B G Ω : Type} [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ ψ : B →+* Ω)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B)) (hk : RingHom.ker φ = RingHom.ker ψ) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  let Q : Ideal B := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  let P : Ideal A := Q.under A
  haveI : Q.LiesOver P := ⟨rfl⟩
  let φb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q φ (fun a ha => ha)
  let ψb : B ⧸ Q →+* Ω := Ideal.Quotient.lift Q ψ (fun a ha => by
    have : a ∈ RingHom.ker ψ := hk ▸ ha
    exact this)
  have φm : ∀ b, φb (Ideal.Quotient.mk Q b) = φ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have ψm : ∀ b, ψb (Ideal.Quotient.mk Q b) = ψ b := fun b => Ideal.Quotient.lift_mk _ _ _
  have inj : ∀ f : B ⧸ Q →+* Ω, (∀ b, f (Ideal.Quotient.mk Q b) = 0 → b ∈ Q) → Function.Injective f := by
    intro f hf
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hf b hx)
  have φi : Function.Injective φb := inj φb fun b hb => by
    rw [φm] at hb
    exact hb
  have ψi : Function.Injective ψb := inj ψb fun b hb => by
    rw [ψm] at hb
    have h' : b ∈ RingHom.ker ψ := hb
    rw [← hk] at h'
    exact h'
  have hr : ψb.range = φb.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) φ ψ h b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨g, hg⟩ := root_orbit (G := G) ψ φ h.symm b
      exact ⟨Ideal.Quotient.mk Q (g • b), by rw [φm, ψm, hg]⟩
  let eφ : B ⧸ Q ≃+* φb.range := RingEquiv.ofBijective φb.rangeRestrict
    ⟨fun x y e => φi (congrArg Subtype.val e), φb.rangeRestrict_surjective⟩
  let eψ : B ⧸ Q ≃+* ψb.range := RingEquiv.ofBijective ψb.rangeRestrict
    ⟨fun x y e => ψi (congrArg Subtype.val e), ψb.rangeRestrict_surjective⟩
  let τ0 : B ⧸ Q ≃+* B ⧸ Q := (eψ.trans (RingEquiv.subringCongr hr)).trans eφ.symm
  have hτ : ∀ x, φb (τ0 x) = ψb x := by
    intro x
    have e : eφ (τ0 x) = RingEquiv.subringCongr hr (eψ x) := eφ.apply_symm_apply _
    exact congrArg Subtype.val e
  let τ : (B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := τ0) (fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply φi
    rw [hτ]
    change ψb (Ideal.Quotient.mk Q (algebraMap A B a)) = φb (Ideal.Quotient.mk Q (algebraMap A B a))
    rw [φm, ψm]
    exact (congrArg (fun f => f a) h).symm)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q τ
  refine ⟨g.1, fun b => ?_⟩
  have e1 : Ideal.Quotient.stabilizerHom Q P G g (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g.1 • b) :=
    Ideal.Quotient.stabilizerHom_apply Q P G g b
  rw [hg] at e1
  have e2 := hτ (Ideal.Quotient.mk Q b)
  rw [ψm] at e2
  rw [← e2, ← φm]
  exact congrArg φb e1

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.invTrans_of :
    InvTrans := by
  intro A B G Ω _ _ _ _ _ _ _ _ _ φ φ' h
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  haveI : (RingHom.ker φ').IsPrime := RingHom.ker_isPrime φ'
  have hu : (RingHom.ker φ).under A = (RingHom.ker φ').under A := by
    ext a
    change φ (algebraMap A B a) = 0 ↔ φ' (algebraMap A B a) = 0
    rw [show φ (algebraMap A B a) = φ' (algebraMap A B a) from congrArg (fun f => f a) h]
  obtain ⟨g0, hg0⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G _ _ hu
  let ψ : B →+* Ω := φ'.comp (MulSemiringAction.toRingHom G B g0)
  have hψ : ∀ b, ψ b = φ' (g0 • b) := fun _ => rfl
  have hk : RingHom.ker φ = RingHom.ker ψ := by
    ext b
    have e : g0 • b ∈ RingHom.ker φ' ↔ b ∈ RingHom.ker φ := by
      rw [hg0]
      exact Ideal.smul_mem_pointwise_smul_iff
    rw [← e, RingHom.mem_ker, RingHom.mem_ker, hψ]
  have hA : φ.comp (algebraMap A B) = ψ.comp (algebraMap A B) := by
    ext a
    have e : φ (algebraMap A B a) = φ' (algebraMap A B a) := congrArg (fun f => f a) h
    simp [hψ, e, smul_algebraMap]
  obtain ⟨g, hg⟩ := same_ker (G := G) φ ψ hA hk
  refine ⟨g * g0⁻¹, fun b => ?_⟩
  have e := hg (g0⁻¹ • b)
  rw [hψ, smul_inv_smul, ← mul_smul] at e
  exact e
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
end
