module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle012
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle010
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle019
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle017
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Noetherian.Nilpotent
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

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalPts

variable {O : Type} [CommRing O] {d : ℕ}

private theorem hasSub {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private def evA {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS O m d →ₐ[O] PS O n d :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem evA_apply {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d) : evA a ha f = ev a f := by
  unfold evA ev
  rw [MvPowerSeries.coe_substAlgHom]

private theorem ev_X {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    ev a (MvPowerSeries.X q) = a q.1 q.2 := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_ev {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem c1 {n : ℕ} {a : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  exact ha j

private theorem c2 {n : ℕ} {a b : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  · exact ha j
  · exact hb j

private theorem cpt {n : ℕ} (i : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt O d i j) = 0 := by
  intro j
  simp [pt]

private def origin (O : Type) [CommRing O] (d : ℕ) : PS O 1 d →ₐ[O] O :=
  { (MvPowerSeries.constantCoeff : PS O 1 d →+* O) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

private theorem general
    (hE : ∀ (n : ℕ) (c : Fin n × Fin d → O), (∀ q, ¬ IsUnit (c q)) →
      ∃! Φ : PS O n d →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q)
    (hN : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (f : PS O n d), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f))
    (F : FGLaw O d) :
    ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst
      (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧
      (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧
      ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  have hX : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) q, ¬ IsUnit (Φ (MvPowerSeries.X q)) :=
    fun n Φ q => hN n Φ _ (by simp)
  have hext : ∀ (n : ℕ) (Φ Ψ : PS O n d →ₐ[O] O),
      (∀ i j, Φ (MvPowerSeries.X (i, j)) = Ψ (MvPowerSeries.X (i, j))) → Φ = Ψ :=
    fun n Φ Ψ h => (hE n _ (hX n Ψ)).unique (fun q => h q.1 q.2) (fun _ => rfl)
  have hext1 : ∀ (Φ Ψ : PS O 1 d →ₐ[O] O),
      (∀ j, Φ (MvPowerSeries.X (0, j)) = Ψ (MvPowerSeries.X (0, j))) → Φ = Ψ :=
    fun Φ Ψ h => hext 1 Φ Ψ (fun i j => by rw [Subsingleton.elim i 0]; exact h j)
  have hK : ∀ (m n : ℕ) (Φ : PS O n d →ₐ[O] O) (Ψ : PS O m d →ₐ[O] O) (a : Fin m → Pt O n d),
      (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) →
      (∀ i j, Ψ (MvPowerSeries.X (i, j)) = Φ (a i j)) → ∀ f, Ψ f = Φ (ev a f) := by
    intro m n Φ Ψ a ha h f
    have : Ψ = Φ.comp (evA a ha) := hext m _ _ (fun i j => by
      rw [AlgHom.comp_apply, evA_apply, ev_X a ha, h])
    rw [this, AlgHom.comp_apply, evA_apply]
  have hP : ∀ (n : ℕ) (φ : Fin n → (PS O 1 d →ₐ[O] O)), ∃ Φ : PS O n d →ₐ[O] O,
      ∀ i j, Φ (MvPowerSeries.X (i, j)) = φ i (MvPowerSeries.X (0, j)) := by
    intro n φ
    obtain ⟨Φ, h, -⟩ := hE n (fun q => φ q.1 (MvPowerSeries.X (0, q.2))) (fun q => hX 1 _ _)
    exact ⟨Φ, fun i j => h (i, j)⟩
  choose P hP using hP
  have cF : ∀ i j, MvPowerSeries.constantCoeff ((![F.F] : Fin 1 → Pt O 2 d) i j) = 0 := c1 F.const
  let add : (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) :=
    fun φ φ' => (P 2 ![φ, φ']).comp (evA ![F.F] cF)
  have hadd : ∀ φ φ' f, add φ φ' f = P 2 ![φ, φ'] (ev (n := 2) ![F.F] f) := by
    intro φ φ' f
    simp only [add, AlgHom.comp_apply, evA_apply]
  have haddX : ∀ φ φ' j, add φ φ' (MvPowerSeries.X (0, j)) = P 2 ![φ, φ'] (F.F j) := by
    intro φ φ' j
    rw [hadd, ev_X _ cF]
    rfl
  have hS : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O) (a b : Pt O n d),
      (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (∀ j, MvPowerSeries.constantCoeff (b j) = 0) →
      (∀ j, φ (MvPowerSeries.X (0, j)) = Φ (a j)) → (∀ j, φ' (MvPowerSeries.X (0, j)) = Φ (b j)) →
      ∀ j, add φ φ' (MvPowerSeries.X (0, j)) = Φ (ev ![a, b] (F.F j)) := by
    intro n Φ φ φ' a b ha hb h h' j
    rw [haddX]
    refine hK 2 n Φ _ _ (c2 ha hb) (fun i k => ?_) _
    rw [hP]
    fin_cases i
    · exact h k
    · exact h' k
  have h0 : ∀ f, origin O d f = MvPowerSeries.constantCoeff f := fun _ => rfl
  have hcomm : ∀ φ φ', add φ φ' = add φ' φ := by
    intro φ φ'
    refine hext1 _ _ (fun j => ?_)
    rw [hS 2 (P 2 ![φ, φ']) φ' φ (pt O d 1) (pt O d 0) (cpt 1) (cpt 0)
      (fun k => (hP 2 ![φ, φ'] 1 k).symm) (fun k => (hP 2 ![φ, φ'] 0 k).symm), F.comm, haddX]
  have hzero : ∀ φ, add (origin O d) φ = φ := by
    intro φ
    refine hext1 _ _ (fun j => ?_)
    rw [hS 1 φ (origin O d) φ 0 (pt O d 0) (fun _ => by simp) (cpt 0)
      (fun k => by simp [h0]) (fun k => rfl), F.unit]
  have hassoc : ∀ φ φ' φ'', add (add φ φ') φ'' = add φ (add φ' φ'') := by
    intro φ φ' φ''
    refine hext1 _ _ (fun j => ?_)
    have e0 := fun k => (hP 3 ![φ, φ', φ''] 0 k).symm
    have e1 := fun k => (hP 3 ![φ, φ', φ''] 1 k).symm
    have e2 := fun k => (hP 3 ![φ, φ', φ''] 2 k).symm
    rw [hS 3 (P 3 ![φ, φ', φ'']) (add φ φ') φ'' (fun l => ev (n := 3) ![pt O d 0, pt O d 1] (F.F l)) (pt O d 2)
        (fun l => const_ev _ (c2 (cpt 0) (cpt 1)) _ (F.const l)) (cpt 2)
        (hS 3 _ φ φ' _ _ (cpt 0) (cpt 1) e0 e1) e2,
      hS 3 (P 3 ![φ, φ', φ'']) φ (add φ' φ'') (pt O d 0) (fun l => ev (n := 3) ![pt O d 1, pt O d 2] (F.F l))
        (cpt 0) (fun l => const_ev _ (c2 (cpt 1) (cpt 2)) _ (F.const l))
        e0 (hS 3 _ φ' φ'' _ _ (cpt 1) (cpt 2) e1 e2), F.assoc]
  letI : Add (PS O 1 d →ₐ[O] O) := ⟨add⟩
  letI : Zero (PS O 1 d →ₐ[O] O) := ⟨origin O d⟩
  letI inst : AddCommMonoid (PS O 1 d →ₐ[O] O) :=
    { add_assoc := hassoc
      zero_add := hzero
      add_zero := fun φ => (hcomm φ _).trans (hzero φ)
      add_comm := hcomm
      nsmul := nsmulRec }
  refine ⟨inst, ?_, h0, ?_⟩
  · intro φ φ' ψ
    change _ ↔ ψ = add φ φ'
    constructor
    · rintro ⟨Φ, h1, h2, h3⟩
      have : Φ = P 2 ![φ, φ'] := by
        refine hext 2 _ _ (fun i j => ?_)
        rw [hP]
        fin_cases i
        · have := h1 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 0))] at this
          exact this
        · have := h2 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 1))] at this
          exact this
      ext1 f
      rw [hadd, ← this, h3]
    · rintro rfl
      refine ⟨P 2 ![φ, φ'], fun f => ?_, fun f => ?_, fun f => (hadd φ φ' f).symm⟩
      · refine (hK 1 2 _ φ _ (c1 (cpt 0)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 0 j).symm
      · refine (hK 1 2 _ φ' _ (c1 (cpt 1)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 1 j).symm
  · intro N φ
    have hmul : ∀ (N : ℕ) j, (N • φ) (MvPowerSeries.X (0, j)) = φ (mulF F.F N j) := by
      intro N
      induction N with
      | zero =>
        intro j
        rw [zero_nsmul]
        change origin O d _ = φ 0
        simp [h0]
      | succ n ih =>
        intro j
        rw [succ_nsmul]
        exact hS 1 φ (n • φ) φ (mulF F.F n) (pt O d 0)
          (GlobalTheory.FormalMul.constantCoeff_mulF F.F F.const n) (cpt 0) ih (fun _ => rfl) j
    have hz : ∀ j, (0 : PS O 1 d →ₐ[O] O) (MvPowerSeries.X (0, j)) = 0 := by
      intro j
      change origin O d _ = 0
      simp [h0]
    constructor
    · intro h j
      rw [← hmul, h, hz]
    · intro h
      exact hext1 _ _ (fun j => by rw [hmul, hz, h j])

theorem points_addCommMonoid : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F
  exact general (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).1)
    (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).2.1) F

end GlobalTheory.FormalPts
end
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def lowZero {A κ : Type} [CommRing A] (e : κ →₀ ℕ) : Ideal (MvPowerSeries κ A) where
  carrier := {g | ∀ e' ≤ e, MvPowerSeries.coeff e' g = 0}
  add_mem' {a b} ha hb e' h := by rw [map_add (f := _), ha e' h, hb e' h, add_zero]
  zero_mem' e' _ := map_zero _
  smul_mem' c x hx e' h := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2 (le_trans (le_of_le_of_eq le_add_self (Finset.HasAntidiagonal.mem_antidiagonal.1 hp)) h), mul_zero]

private theorem coeff_box {A κ : Type} [CommRing A] [Fintype κ] [DecidableEq κ] (N : ℕ) (c : (κ →₀ ℕ) → A)
    (e : κ →₀ ℕ) (he : ∀ i, e i < N) :
    MvPowerSeries.coeff e (∑ b : κ → Fin N, MvPowerSeries.C (c (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
      ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ (b i : ℕ)) = c e := by
  have hm : ∀ b : κ → ℕ, ∏ i, (MvPowerSeries.X i : MvPowerSeries κ A) ^ b i =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm b) 1 := fun b => by
    rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  have he' : (Finsupp.equivFunOnFinite.symm fun i => ((⟨e i, he i⟩ : Fin N) : ℕ)) = e := by
    ext i; rfl

  rw [map_sum, Finset.sum_eq_single (fun i => (⟨e i, he i⟩ : Fin N))]
  · rw [hm, MvPowerSeries.coeff_C_mul, he', MvPowerSeries.coeff_monomial_same, _root_.mul_one]
  · intro b _ hb
    rw [hm, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_monomial_ne, mul_zero]
    intro h
    exact hb (funext fun i => Fin.ext (by simp [h]))
  · simp

theorem eq_of_nv_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  intro R _ I hI n d f f' H
  ext e
  rw [← sub_eq_zero]
  refine hI.haus _ fun k => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  let A := R ⧸ I ^ (k + 1)
  let J : Ideal (MvPowerSeries (Fin n × Fin d) A) := lowZero e
  let N : ℕ := (∑ i, e i) + 1
  have he : ∀ i, e i < N := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have halg : ∀ t : R, algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J) t =
      Ideal.Quotient.mk J (MvPowerSeries.C (Ideal.Quotient.mk (I ^ (k + 1)) t)) := fun t => by
    rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]; rfl
  have hN : ∀ q : Fin n × Fin d, (Ideal.Quotient.mk J (MvPowerSeries.X q)) ^ N = 0 := fun q => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    intro e' h
    exact (MvPowerSeries.X_pow_dvd_iff.1 dvd_rfl) e' (lt_of_le_of_lt (h q) (he q))
  have hv : ∀ g : PS R n d, nv (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)) g
      (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) =
      Ideal.Quotient.mk J (∑ b : Fin n × Fin d → Fin N, MvPowerSeries.C ((fun x => Ideal.Quotient.mk (I ^ (k + 1))
        (MvPowerSeries.coeff x g)) (Finsupp.equivFunOnFinite.symm fun i => (b i : ℕ))) *
        ∏ i, (MvPowerSeries.X i : MvPowerSeries (Fin n × Fin d) A) ^ (b i : ℕ)) := fun g => by
    letI := (algebraMap R (MvPowerSeries (Fin n × Fin d) A ⧸ J)).toAlgebra
    refine (evBasic_nEval_eq_tEval g (fun q : Fin n × Fin d => Ideal.Quotient.mk J (MvPowerSeries.X q)) N hN).trans ?_

    simp only [tEval, map_sum, map_mul, map_prod, map_pow]
    exact Finset.sum_congr rfl fun b _ => congrArg (· * _) (halg _)
  have h := H (MvPowerSeries (Fin n × Fin d) A ⧸ J) k (fun t ht => by
      rw [halg, Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero, map_zero]) (fun hR hne => ?_)
    (fun i j => Ideal.Quotient.mk J (MvPowerSeries.X (i, j))) (fun i j => ⟨N, hN (i, j)⟩)
  · rw [hv, hv, Ideal.Quotient.eq] at h
    have h2 := h e le_rfl
    rw [map_sub, sub_eq_zero] at h2
    exact Ideal.Quotient.eq.1 (((coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f)) e he).symm.trans h2).trans (coeff_box N (fun x => Ideal.Quotient.mk (I ^ (k + 1))
      (MvPowerSeries.coeff x f')) e he))
  · have hA : I ^ (k + 1) ≠ ⊤ := fun h => hne (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero k)))
    haveI : Nontrivial A := Ideal.Quotient.nontrivial_iff.2 hA
    haveI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hJ : J ≠ ⊤ := fun h => by
      have : (1 : MvPowerSeries (Fin n × Fin d) A) ∈ J := h ▸ Submodule.mem_top
      have := this 0 zero_le
      simp at this
    haveI : Nontrivial (MvPowerSeries (Fin n × Fin d) A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ
    refine ⟨IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective, ⟨fun t ht => ?_⟩⟩
    rw [halg] at ht
    have h1 := (IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).map_nonunit _ ht
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_C] at h1
    exact (IsLocalHom.of_surjective (Ideal.Quotient.mk (I ^ (k + 1))) Ideal.Quotient.mk_surjective).map_nonunit _ h1

end GlobalTheory.ChF
end
end

section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def dbl (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))

private theorem mem_dbl {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S] {J : Ideal S}
    {x : S × S} : x ∈ dbl R J ↔ x.1 - x.2 ∈ J := by
  rw [← Ideal.Quotient.eq]; rfl

private theorem exists_coord {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] {d e : ℕ} {F : Fin d → PS R 2 d} {F' : Fin e → PS R 2 e}
    {X : Fam G d} {X' : Fam G' e} (h : NilChart G F X) (h' : NilChart G' F' X') (f : G ⟶ G') [IsMonHom f]
    (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin e → S, (∀ j, IsNilpotent (b j)) ∧ X S a ≫ f = X' S b := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range a).toFinset, by simp [J]⟩, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let ρ : dbl R J →ₐ[R] S := (AlgHom.fst R S S).comp (dbl R J).val
  let τ : dbl R J →ₐ[R] S := (AlgHom.snd R S S).comp (dbl R J).val
  let σ : S →ₐ[R] dbl R J := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun x => by
    simp [mem_dbl])
  have hker : IsNilpotent (RingHom.ker ρ) := by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n + 1, le_bot_iff.1 fun x hx => ?_⟩
    have h1 : x ∈ RingHom.ker ρ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
    have h2 : RingHom.ker ρ ≤ J.comap τ := fun y hy => by
      have h3 := mem_dbl.1 y.2
      have h4 : y.1.1 = 0 := hy
      rw [h4, zero_sub, neg_mem_iff] at h3
      exact h3
    have h5 := Ideal.le_comap_pow τ (n + 1) (Ideal.pow_right_mono h2 (n + 1) hx)
    rw [pow_succ, hn, zero_mul] at h5
    exact Subtype.ext (Prod.ext h1 h5)
  let a' : Fin d → dbl R J := fun i => ⟨(0, a i), mem_dbl.2 (by
    simpa using (Ideal.subset_span ⟨i, rfl⟩ : a i ∈ J))⟩
  have hnil : ∀ y : dbl R J, ρ y = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨n, hn⟩ := hker
    exact ⟨n, by simpa [hn] using Ideal.pow_mem_pow (show y ∈ RingHom.ker ρ from hy) n⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ rfl
  obtain ⟨b, hb, hz⟩ := h'.surj (dbl R J) S ρ σ (by ext; rfl) hker (X _ a' ≫ f) (by
    rw [← Category.assoc, h.nat _ _ ρ a' ha']
    have : (fun i => ρ (a' i)) = 0 := rfl
    rw [this, h.zero, MonObj.one_comp])
  refine ⟨fun j => τ (b j), fun j => (hnil _ (hb j)).map τ, ?_⟩
  rw [← h'.nat _ _ τ b (fun j => hnil _ (hb j)), ← hz, ← Category.assoc, h.nat _ _ τ a' ha']
  rfl

theorem exists_reads : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G'] (d e : ℕ) (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (X : Fam G d) (X' : Fam G' e), NilChart G F X → NilChart G' F' X' → ∀ f : G ⟶ G', IsMonHom f → ∃ φ : Fin e → PS R 1 d, Reads X X' f φ := by
  intro R _ G _ _ G' _ _ d e F F' X X' h h' f hf
  classical
  choose b hb hX using exists_coord h h' f
  let c : Fin e → ∀ (S : Type) [CommRing S] [Algebra R S], (Fin 1 × Fin d → S) → S :=
    fun j S _ _ a => if ha : ∀ i, IsNilpotent (a (0, i)) then b S (fun i => a (0, i)) ha j else 0
  have hc : ∀ j (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S']
      (φ : S →ₐ[R] S') (a : Fin 1 × Fin d → S), (∀ i, IsNilpotent (a i)) →
      φ (c j S a) = c j S' (fun i => φ (a i)) := by
    intro j S _ _ S' _ _ φ a ha
    have h1 : ∀ i, IsNilpotent (a (0, i)) := fun i => ha _
    have h2 : ∀ i, IsNilpotent (φ (a (0, i))) := fun i => (ha _).map φ
    simp only [c, dif_pos h1, dif_pos h2]
    refine congrFun (h'.inj S' (fun j => φ (b S _ h1 j)) (b S' _ h2) (fun j => (hb S _ h1 j).map φ)
      (hb S' _ h2) ?_) j
    rw [← hX, ← h'.nat _ _ φ _ (hb S _ h1), ← hX, ← Category.assoc, h.nat _ _ φ _ h1]
  choose φ hφ using fun j => GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic (c j) (hc j)
  have key : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)),
      b S a ha = fun j => nv (algebraMap R S) (φ j) ![a] := by
    intro S _ inst a ha
    funext j
    have h1 := hφ j S (fun q => a q.2) (fun q => ha _)
    simp only [c, dif_pos ha] at h1
    rw [h1, nv]
    have : (algebraMap R S).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    rw [this]
    congr 1
    funext q
    obtain ⟨i, k⟩ := q
    fin_cases i
    rfl
  refine ⟨φ, fun j => ?_, fun S _ _ a ha => by rw [hX S a ha, key]⟩
  have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R) i) := fun _ => IsNilpotent.zero
  have h1 : b R 0 h0 = 0 := h'.inj R _ _ (hb R 0 h0) (fun _ => IsNilpotent.zero) (by
    rw [← hX, h.zero, h'.zero, MonObj.one_comp])
  have h2 := hφ j R 0 (fun _ => IsNilpotent.zero)
  have h3 : c j R 0 = 0 := by
    exact (dif_pos h0).trans (congrFun h1 j)
  have h4 := (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; simp) : Ideal.span _ ≤ (⊥ : Ideal R))
    (evBasic_nEval_sub_coeff_mem (φ j) (0 : Fin 1 × Fin d → R) (fun _ => IsNilpotent.zero))
  rw [← h2, h3] at h4
  simpa using h4

end GlobalTheory.ChF
end
end
