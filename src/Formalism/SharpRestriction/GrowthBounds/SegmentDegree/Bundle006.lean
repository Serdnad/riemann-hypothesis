module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle003
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def lamG : Fin X.F.J → ℤ × Fin (r + K) → Fin n' × Fin (r + K) := fun _ v => (posOf n' v.1, v.2)

def lamE : Fin X.F.J → ℤ × Fin (r + K) → ℕ := fun j v => p ^ (X.F.dist (j.val : ℤ) v.1 + X.Rj p K (j.val : ℤ))


omit [NeZero n'] in
def lamL (la : Fin n' → Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => la v.1 v.2

def lamS (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) :
    Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | (∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) ∧
    m ∈ segDegSet (r := r) K (X.bfam p K la e (j.val : ℤ)) ∧ m ∈ X.resSet p K (j.val : ℤ)}

end Dat

def RestLamA : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → ∀ (j : ℤ) (b : ℤ → ℕ),
    (∀ x, x ∉ X.F.letters j → b x = 0) →
    ∃ y : Fin (Module.finrank O (X.Mj p K O j b)) → SegRing O r K, (∀ i, y i ∈ X.Mj p K O j b) ∧
      LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (y i)

def RestLamInj (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ la' ∈ X.LA p K, ∀ e' ∈ X.EE p K la',
    ∀ m m' : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) → (∀ j, m' j ∈ X.lamS p K la' e' j) →
      Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) =
        Dat.lamL K la' + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m' j) → (la = la' ∧ e = e') ∧ m = m'

def RestLamDeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, X.IsCLabel p K (Dat.lamL K la) ∧
    ∀ m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) →
      ∀ t, ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = X.a' p K t

theorem lam_map_phc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : Fin X.F.J) (P : SegRing R r K) :
    MvPolynomial.map f (X.phc p K R (j.val : ℤ) P) = lam_ph (X.lamG K) (X.lamE p K) j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Dat.phc, lam_ph]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [Dat.phc, lam_ph, Dat.lamG, Dat.lamE]

theorem lam_mem_lamS {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K] (O : Type) [CommRing O]
    (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) {y : SegRing O r K}
    (hy : y ∈ X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) : y ∈ restrictSupport O (X.lamS p K la e j) := by
  classical
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hs := XX'_supported O X.F (j.val : ℤ) _ _ _ h1
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ y.support := Finset.mem_coe.mp hm
  refine ⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm,
    (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩
  have hvars : v ∈ y.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩
  exact (MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)

theorem restLam_of_rests (C₀ : ℝ) (hA : RestLamA) (hI : RestLamInj C₀) (hD : RestLamDeg C₀) : RestLam C₀ := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX hLa hk
  classical
  let SS := (X.LA p K).sigma fun la => X.EE p K la
  let Φ := {x // x ∈ SS}
  have hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1 := fun f => Finset.mem_sigma.mp f.2
  let nn : Φ → Fin X.F.J → ℕ := fun f j =>
    Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))
  have hex := fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ))
    (fun x hx => by simp [Dat.bfam, hx])
  choose y hyM hyL using hex
  set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres
  have hli := lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1)
    (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i))
    (fun f j => hyL f j)
    (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j i)))
    (by
      intro f f' m m' hm hm' h
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2
        m m' hm hm' h
      refine ⟨Subtype.ext ?_, h3⟩
      obtain ⟨⟨la, e⟩, hf⟩ := f
      obtain ⟨⟨la', e'⟩, hf'⟩ := f'
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

  have hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)),
      monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈
        X.LamBar p K O := by
    rintro ⟨f, a⟩
    let Yf : Fin X.F.J → SegRing O r K := fun i => y f i (a i)
    let y' : ℤ → SegRing O r K := fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0
    have hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i := by
      intro i
      have h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J := ⟨by positivity, by simpa using i.isLt⟩
      simp only [y', dif_pos h]
      exact congrArg Yf (Fin.ext (by simp))
    obtain ⟨hlab, hdeg⟩ := hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2
    have hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) =
        ∏ j : Fin X.F.J, lam_ph (R := O) (X.lamG K) (X.lamE p K) j (Yf j) := by
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hy'i]
      rfl
    refine Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) *
      monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩
    · intro j
      by_cases h : 0 ≤ j ∧ j.toNat < X.F.J
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
        have hk' : k < X.F.J := by simpa using h.2
        have := hy'i ⟨k, hk'⟩
        simp only at this
        rw [this]
        exact hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)
      · simp only [y', dif_neg h]
        exact Submodule.zero_mem _
    · rw [hprod, lam_expand]
      unfold RRdeg
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro n hn
      have hn' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
      rw [mul_comm, coeff_monomial_mul'] at hn'
      split_ifs at hn' with hle
      · rw [one_mul, coeff_sum] at hn'
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        rw [coeff_monomial] at hm0
        split_ifs at hm0 with heq
        · have hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) := by
            rw [heq]; exact (add_tsub_cancel_of_le hle).symm
          intro t
          rw [hn2]
          refine hdeg m (fun j => ?_) t
          exact (MvPolynomial.mem_restrictSupport_iff (R := O)).mp
            (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · exact absurd rfl hm0
      · exact absurd rfl hn'
    · rw [map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [lam_map_phc, hy'i]
  have hfin : Module.Finite (FF O) (X.LamBar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_
    unfold Dat.LamBar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨_, _, _, -, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) =>
      (⟨_, hmem x⟩ : X.LamBar p K O)) := by
    refine LinearIndependent.of_comp (X.LamBar p K O).subtype ?_
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  refine le_trans (le_of_eq ?_) hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la)
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]
  exact (Finset.sum_coe_sort SS
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def ColumnWordReductionLifts (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ), X.IsEll p K j e → X.Step2 p K j b →
    ∀ q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j),
    ∀ I' I'', IsSt q.1 I' → IsSt q.2 I'' →
      ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
        MvPolynomial.map (IsLocalRing.residue O)
          (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e)

theorem map_suppProj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    (A : MvPolynomial σ R) : MvPolynomial.map f (suppProj R s A) = suppProj S s (MvPolynomial.map f A) := by
  classical
  ext m
  rw [coeff_map, coeff_suppProj, coeff_suppProj, coeff_map]
  split_ifs <;> simp

theorem plEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    (hA : A ∈ Pol R r d) : plEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold plEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.castAdd K c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.natAdd r c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, add_zero]

theorem nmEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin K) R}
    (hA : A ∈ Pol R K d) : nmEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold nmEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.natAdd r c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.castAdd K c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, zero_add]

theorem geR_mono {v v' : WithTop ℤ} {t : ℝ} (h : geR v t) (hv : v ≤ v') : geR v' t := by
  intro z hz
  rw [hz] at hv
  induction v using WithTop.recTopCoe with
  | top => simp at hv
  | coe z0 =>
    have h1 : z0 ≤ z := WithTop.coe_le_coe.mp hv
    exact (h z0 rfl).trans (by exact_mod_cast h1)

theorem XX'_polComp (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ) (β : ℤ → ℕ) {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) :
    polComp O (r + K) β x ∈ XX' O r K F j m th o := by
  classical
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' := hx2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · clear hx hx2 hx2'
    induction hx1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, G, M, hA, hG, hc, rfl⟩ := hy
      obtain ⟨T', hT'⟩ := exists_sum_polComp O r A
      obtain ⟨T'', hT''⟩ := exists_sum_polComp O K G
      have hsum : plEmb O r K A * nmEmb O r K G = ∑ d' ∈ T', ∑ d'' ∈ T'',
          plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) := by
        conv_lhs => rw [hT', hT'']

        rw [map_sum, map_sum, Finset.sum_mul_sum]

      rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun d' _ => ?_

      rw [map_sum]
      refine Submodule.sum_mem _ fun d'' _ => ?_
      have hP : plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) ∈ Pol O (r + K) (d' + d'') :=
        hom_Pol_mul O (plEmb_Pol r K (polComp_mem_Pol O r d' A)) (nmEmb_Pol r K (polComp_mem_Pol O K d'' G))
      by_cases hd : β = d' + d''
      · rw [hd, polComp_of_mem O _ _ _ hP]
        refine Submodule.subset_span ⟨_, _, M, polComp_mem_supported O r d' A _ hA,
          polComp_mem_supported O K d'' G _ hG, fun x hx hW => ?_, rfl⟩
        obtain ⟨cE, cO, cR⟩ := hc x hx hW
        exact ⟨fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cE he).1, (cE he).2.trans (valS_le_polComp _ _ d' A)⟩,
          fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cO he).1, (cO he).2.trans (valS_le_polComp _ _ d' A)⟩,
          geR_mono cR (valS_le_polComp _ _ d' A)⟩
      · rw [polComp_of_ne O _ _ _ _ hP hd]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  · rw [mem_restrictSupport_iff] at hx2 ⊢
    intro mm hmm
    exact hx2 (Finset.mem_coe.mpr (suppProj_support_subset O _ x (Finset.mem_coe.mp hmm)))

theorem zSeg_add {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ)
    (y1 y2 : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (y1 + y2) e = X.zSeg p K O j y1 e + X.zSeg p K O j y2 e := by
  unfold Dat.zSeg; rw [map_add (f := _)]; ring

theorem zSeg_smul {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (c : O)
    (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (c • y) e = c • X.zSeg p K O j y e := by
  unfold Dat.zSeg; rw [map_smul, mul_smul_comm, smul_mul_assoc]

theorem segment_reduction_of_column_words (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (hW : ColumnWordReductionLifts C₀) : SegmentReductionLiftsMultihomogeneous C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b y e hy he h2 β hβ
  have : Fact p.Prime := ⟨hX.prime⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h1 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hseg
    (fun _ => Int.natCast_nonneg _)).1
  have hy1 : y ∈ XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) := hy.1.1
  rw [h1] at hy1
  unfold Formalism.MainNotions.CovariantDegrees.XXZ at hy1
  rw [Submodule.map_span] at hy1
  have key : ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
      MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e) := by
    clear hβ hy
    induction hy1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩ := hy
      exact hW p n' r K X O S hX hLa hk j b e he h2 q hq I' I'' hI' hI''
    | zero => exact ⟨0, Submodule.zero_mem _, by simp [Dat.zSeg]⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, hx1, e1⟩ := hy
      obtain ⟨x2, hx2, e2⟩ := hz
      exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, by rw [zSeg_add, map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, hx1, e1⟩ := hy
      refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
      rw [zSeg_smul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, e1]
  obtain ⟨x, hx, hxe⟩ := key
  refine ⟨polComp O (r + K) β x, XX'_polComp O r K X.F j _ _ _ β hx, polComp_mem_Pol O _ β x, ?_⟩
  unfold polComp
  rw [map_suppProj, hxe, ← map_suppProj]
  congr 1
  exact polComp_of_mem O _ β _ hβ

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
