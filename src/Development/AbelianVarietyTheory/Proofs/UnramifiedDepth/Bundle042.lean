module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle035
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle037
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle038
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.ChF

namespace GlobalTheory.ChF

private theorem coeff_eq_zero_of_roots {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ]
    [DecidableEq σ] {N : ℕ} {ζ : O} (hζ : IsPrimitiveRoot ζ N) (c : (σ → Fin N) → O)
    (h : ∀ b : σ → ℕ, ∑ a : σ → Fin N, c a * ∏ i, (ζ ^ b i) ^ (a i : ℕ) = 0) : ∀ a, c a = 0 := by
  let χ : (σ → Fin N) → (Multiplicative (σ → ℕ) →* O) := fun a =>
    { toFun := fun b => ∏ i, (ζ ^ (Multiplicative.toAdd b) i) ^ (a i : ℕ)
      map_one' := by simp
      map_mul' := fun b b' => by
        simp [pow_add, mul_pow, Finset.prod_mul_distrib] }
  have hinj : Function.Injective χ := by
    intro a a' haa
    funext j
    have h1 := DFunLike.congr_fun haa (Multiplicative.ofAdd (Pi.single j 1))
    have key : ∀ e : σ → Fin N, χ e (Multiplicative.ofAdd (Pi.single j 1)) = ζ ^ (e j : ℕ) := by
      intro e
      show ∏ i, (ζ ^ (Pi.single j 1 : σ → ℕ) i) ^ (e i : ℕ) = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    rw [key, key] at h1
    exact Fin.ext (hζ.pow_inj (a j).2 (a' j).2 h1)
  have hli := (linearIndependent_monoidHom (Multiplicative (σ → ℕ)) O).comp χ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli c
  funext b
  have := h (Multiplicative.toAdd b)
  simpa [Finset.sum_apply, χ] using this

private theorem map_coe_mem_span {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {σ : Type}
    [Fintype σ] [DecidableEq σ] {N : ℕ} (hN : 0 < N) (ψ : MvPowerSeries σ O →ₐ[O] Q)
    (hy : ∀ i, (1 + ψ (MvPowerSeries.X i)) ^ N = 1) (P : MvPolynomial σ O) :
    ψ (P : MvPowerSeries σ O) ∈ Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) := by
  set S := Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) with hS
  have hmon : ∀ e : σ → ℕ, ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (e i) ∈ S := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % N, Nat.mod_lt _ hN⟩, ?_⟩
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (pow_eq_pow_mod (e i) (hy i)).symm
  have hmul : ∀ j, ∀ q ∈ S, q * (1 + ψ (MvPowerSeries.X j)) ∈ S := by
    intro j q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := hmon (fun i => (a i : ℕ) + (Pi.single j 1 : σ → ℕ) i)
      simp only [pow_add, Finset.prod_mul_distrib] at this
      rwa [Finset.prod_eq_single j (f := fun i =>
        (1 + ψ (MvPowerSeries.X i)) ^ (Pi.single j 1 : σ → ℕ) i)
        (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp), Pi.single_eq_same, pow_one] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact S.smul_mem a hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : Q) ∈ S := by simpa using hmon 0
    have : ψ ((MvPolynomial.C a : MvPolynomial σ O) : MvPowerSeries σ O) = a • (1 : Q) := by
      rw [MvPolynomial.coe_C, ← Algebra.algebraMap_eq_smul_one]
      exact ψ.commutes a
    rw [this]
    exact S.smul_mem a h1
  | add f g hf hg => rw [MvPolynomial.coe_add, map_add (f := _)]; exact S.add_mem hf hg
  | mul_X f j hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]
    have := S.sub_mem (hmul j _ hf) hf
    convert this using 1
    ring

private theorem exists_pow_eq {A : Type} [CommRing A] {p : ℕ} (hp : p.Prime) (k : ℕ) (x : A) :
    ∃ s : A, x ^ p ^ k = ((1 + x) ^ p ^ k - 1) + (p : A) * s := by
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp (1 : A) x k
  refine ⟨-(x * s), ?_⟩
  rw [hs]
  ring

private theorem exists_primitiveRoot_integers {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {N : ℕ}
    (hN : 0 < N) : ∃ ζ : O, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C N
  have hvz : v z ≤ 1 := by
    have : v z ^ N = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hN.ne').1 this).le
  obtain ⟨ζ, rfl⟩ := hv.exists_of_le_one hvz
  exact ⟨ζ, hz.of_map_of_injective hv.hom_inj⟩

theorem fh_gmF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  intro p hp C _ _ _ v O _ _ hv _ hc r k
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain _
  have hN : 0 < p ^ k := pow_pos hp.out.pos k
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_integers hv hN
  have hmul := (gmLaw_chars_mul O r).2.2 (p ^ k)
  set I : Ideal (PS O 1 r) := Ideal.span (Set.range (mulF (gmF O r) (p ^ k))) with hI
  have hrel : ∀ i : Fin 1 × Fin r, (1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1 ∈ I := by
    rintro ⟨i0, i⟩
    obtain rfl : i0 = 0 := Subsingleton.elim _ _
    exact Ideal.subset_span ⟨i, hmul i⟩

  obtain ⟨M, hM⟩ : ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin r → PS O 1 r)) ^ M ≤
      I ⊔ Ideal.map (MvPowerSeries.C : O →+* PS O 1 r) (Ideal.span {(p : O)}) := by
    apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (MvPowerSeries.X i : PS O 1 r)
    refine ⟨p ^ k, ?_⟩
    rw [hs]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (hrel i)) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_))
    rw [← map_natCast (MvPowerSeries.C : O →+* PS O 1 r) p]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  let π : PS O 1 r →ₐ[O] (PS O 1 r ⧸ I) := Ideal.Quotient.mkₐ O I
  let m : (Fin 1 × Fin r → Fin (p ^ k)) → (PS O 1 r ⧸ I) :=
    fun a => ∏ i, (1 + π (MvPowerSeries.X i)) ^ (a i : ℕ)
  have hspan : ∀ q : PS O 1 r ⧸ I, q ∈ Submodule.span O (Set.range m) := by
    intro q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨P, -, hP⟩ := GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O
      (Ideal.span {(p : O)}) (Submodule.fg_span (Set.finite_singleton _)) hc (Fin 1 × Fin r) (Fin r)
      (mulF (gmF O r) (p ^ k)) M hM g
    rw [Ideal.Quotient.eq.2 hP]
    refine map_coe_mem_span hN π (fun i => ?_) P
    have h0 : π ((1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hrel i)
    rw [map_sub, map_pow, map_add (f := _), map_one] at h0
    exact sub_eq_zero.1 h0

  have hpt : ∀ b : Fin 1 × Fin r → ℕ, ∃ φ : (PS O 1 r ⧸ I) →ₐ[O] O,
      ∀ i, φ (π (MvPowerSeries.X i)) = ζ ^ b i - 1 := by
    intro b
    have hone : ∀ i, (1 + (ζ ^ b i - 1)) ^ p ^ k - 1 = 0 := by
      intro i
      rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    obtain ⟨ψ, hψ⟩ := (GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) (Fin 1 × Fin r)
      (fun i => ζ ^ b i - 1) (fun i => by
        obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (ζ ^ b i - 1)
        refine ⟨p ^ k, ?_⟩
        rw [hs, hone, zero_add]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hc O
    have hker : I ≤ RingHom.ker ψ := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show ψ _ = 0
      rw [hmul, map_sub, map_pow, map_add (f := _), map_one, hψ]
      exact hone _
    exact ⟨Ideal.Quotient.liftₐ I ψ (fun a ha => hker ha), fun i => hψ i⟩
  have hsep : ∀ c : (Fin 1 × Fin r → Fin (p ^ k)) → O,
      (∀ φ : (PS O 1 r ⧸ I) →ₐ[O] O, φ (∑ a, c a • m a) = 0) → ∀ a, c a = 0 := by
    intro c hcφ
    refine coeff_eq_zero_of_roots hζ c fun b => ?_
    obtain ⟨φ, hφ⟩ := hpt b
    have := hcφ φ

    simpa only [map_sum, map_smul, m, map_prod, map_pow, map_add (f := _), map_one, hφ, add_sub_cancel,
    smul_eq_mul] using this
  have hli : LinearIndependent O m := by
    rw [Fintype.linearIndependent_iff]
    intro c h0
    exact hsep c fun φ => by rw [h0, map_zero]
  let B := Module.Basis.mk hli (fun q _ => hspan q)
  refine ⟨Module.Free.of_basis B, Module.Finite.of_basis B, fun q hq => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hspan q)
  simp [hsep c hq]

end GlobalTheory.ChF
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

section
variable {R : Type} [CommRing R] (I : Ideal R) (n d : ℕ)

private abbrev MainNotions (k : ℕ) : Type :=
  Geo.Tor.JetR R (Fin n × Fin d) k ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k))

private def xK (k : ℕ) : Fin n → Fin d → MainNotions I n d k := fun i j =>
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))

private abbrev JJ : Ideal (PS R n d) :=
  I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n × Fin d) R) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) R))

variable {n d}

private def Lev (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S) : Prop :=
  Kills I k S ∧ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2) ^ (k + 1) = ⊥

variable {I}

private theorem Lev.mono {k k' : ℕ} (h : k ≤ k') {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) : Lev I k' S a :=
  ⟨fun t ht => ha.1 t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans ha.2.le)⟩

private theorem Lev.nil {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (i : Fin n) (j : Fin d) : IsNilpotent (a i j) := by
  refine ⟨k + 1, ?_⟩
  rw [← Ideal.mem_bot, ← ha.2]
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (f := fun q : Fin n × Fin d => a q.1 q.2) (i, j))) _

private theorem exists_lev {S : Type} [CommRing S] [Algebra R S] {a : Fin n → Fin d → S}
    (hk : ∃ k, Kills I k S) (ha : ∀ i j, IsNilpotent (a i j)) : ∃ k, Lev I k S a := by
  obtain ⟨k, hk⟩ := hk
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (I := Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) (J := ⊥)
    (Ideal.span_le.2 (by rintro _ ⟨q, rfl⟩; exact ha q.1 q.2))
    (Submodule.fg_span (Set.finite_range _))
  exact ⟨k + m, fun t ht => hk t (Ideal.pow_le_pow_right (by omega) ht),
    le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hm)⟩

private theorem exists_lift {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) :
    ∃ φ : MainNotions I n d k →ₐ[R] S, ∀ i j, φ (xK I n d k i j) = a i j := by
  let φ₀ : Geo.Tor.JetR R (Fin n × Fin d) k →ₐ[R] S :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q : Fin n × Fin d => a q.1 q.2)
      (aeval_kill k _ _ (fun q => Ideal.subset_span (Set.mem_range_self q)) ha.2)
  refine ⟨Ideal.Quotient.liftₐ _ φ₀ fun y hy => ?_, fun i j => ?_⟩
  · have : (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)) ≤
        RingHom.ker φ₀.toRingHom := by
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (φ₀.commutes t).trans (ha.1 t ht)
    exact this hy
  · exact MvPolynomial.aeval_X (fun q : Fin n × Fin d => a q.1 q.2) (i, j)

private theorem lev_xK (k : ℕ) : Lev I k (MainNotions I n d k) (xK I n d k) := by
  refine ⟨fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ht), ?_⟩
  have h := congrArg (Ideal.map (Ideal.Quotient.mk
    ((I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) k)))))
    (jet_aug_pow (T := R) (Fin n × Fin d) k)
  rw [Ideal.map_pow _ (Ideal.map _ (Ideal.span _)), Ideal.map_bot, Ideal.map_span, Ideal.map_span, ← Set.range_comp,
    ← Set.range_comp] at h
  exact h

private theorem hom_coe {S : Type} [CommRing S] [Algebra R S] (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c) (p : MvPolynomial (Fin n × Fin d) R) :
    ψ (p : MvPowerSeries (Fin n × Fin d) R) =
      MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.coe_C, MvPolynomial.aeval_C]; exact hC c
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp => rw [MvPolynomial.coe_mul, map_mul, map_mul, hp, MvPolynomial.coe_X, MvPolynomial.aeval_X]

private theorem hom_kill {k : ℕ} {S : Type} [CommRing S] [Algebra R S]
    {a : Fin n → Fin d → S} (ha : Lev I k S a) (ψ : PS R n d →+* S)
    (hC : ∀ c, ψ (MvPowerSeries.C c) = algebraMap R S c)
    (hX : ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) (g : PS R n d)
    (hg : g ∈ JJ I n d ^ (k + 1 + (k + 1))) : ψ g = 0 := by
  have h1 : JJ I n d ^ (k + 1 + (k + 1)) ≤ RingHom.ker ψ := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le ?_ ?_)
    · rw [← Ideal.map_pow]
      refine Ideal.map_le_iff_le_comap.2 fun t ht => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact (hC t).trans (ha.1 t ht)
    · rw [RingHom.ker, ← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, ← Set.range_comp,
        ← ha.2]
      exact le_of_eq (by congr 3; exact funext hX)
  exact h1 hg

private theorem exists_poly (N : ℕ) (g : PS R n d) :
    ∃ p : MvPolynomial (Fin n × Fin d) R, g - (p : MvPowerSeries (Fin n × Fin d) R) ∈ JJ I n d ^ N := by
  refine ⟨MvPowerSeries.truncTotal N g,
    ((mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).1 N _).2 fun e => ?_⟩
  by_cases he : e.degree < N
  · rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ he, sub_self]
    exact Ideal.zero_mem _
  · rw [show N - e.degree = 0 by omega]
    simp

private theorem nv_lift {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') {a : Fin n → Fin d → S} (ha : ∀ i j, IsNilpotent (a i j)) (g : PS R n d) :
    φ (nv (algebraMap R S) g a) = nv (algebraMap R S') g (fun i j => φ (a i j)) := by
  have h := (nv_calculus R S (algebraMap R S) n d a ha).2.2.2.2.1 S' φ.toRingHom g
  rw [show φ.toRingHom.comp (algebraMap R S) = algebraMap R S' from RingHom.ext φ.commutes] at h
  exact h

private theorem mem_of_nv_eq (k : ℕ) (g g' : PS R n d)
    (h : nv (algebraMap R _) g (xK I n d k) = nv (algebraMap R _) g' (xK I n d k)) :
    g - g' ∈ JJ I n d ^ (k + 1) := by
  let π : PS R n d →+* PS R n d ⧸ JJ I n d ^ (k + 1) := Ideal.Quotient.mk _
  have hπC : ∀ c, π (MvPowerSeries.C c) = algebraMap R _ c := fun c => rfl
  have hl : Lev I k (PS R n d ⧸ JJ I n d ^ (k + 1)) (fun i j => π (MvPowerSeries.X (i, j))) := by
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [← hπC]
      refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_right_mono le_sup_left _ ?_)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ht
    · rw [← le_bot_iff, ← Ideal.map_quotient_self (JJ I n d ^ (k + 1)), Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.span_le.2 ?_) _
      rintro _ ⟨q, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨φ, hφ⟩ := exists_lift hl
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ hl.nil).1
  have hψπ : ∀ u, ψ u = π u := fun u => by
    obtain ⟨p, hp⟩ := exists_poly (I := I) (k + 1 + (k + 1)) u
    have h1 := hom_kill hl ψ hC hX _ hp
    have h2 := hom_kill hl π hπC (fun _ => rfl) _ hp
    rw [map_sub, sub_eq_zero] at h1 h2
    rw [h1, h2, hom_coe ψ hC, hom_coe π hπC]
    simp only [hX]
  have h3 := congrArg φ h
  rw [nv_lift φ (lev_xK k).nil, nv_lift φ (lev_xK k).nil] at h3
  simp only [hφ] at h3
  rw [← hψ, ← hψ, hψπ, hψπ] at h3
  exact Ideal.Quotient.eq.1 h3

private theorem nv_surj (k : ℕ) (y : MainNotions I n d k) :
    ∃ g : PS R n d, nv (algebraMap R _) g (xK I n d k) = y := by
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil).1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨(p : MvPowerSeries (Fin n × Fin d) R), ?_⟩
  rw [← hψ, hom_coe ψ hC]
  have : MvPolynomial.aeval (fun q => ψ (MvPowerSeries.X q)) =
      (Ideal.Quotient.mkₐ R _).comp (Ideal.Quotient.mkₐ R _) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [MvPolynomial.aeval_X, hX]
    rfl
  rw [this]
  rfl

private theorem const_add_nil (k : ℕ) (y : MainNotions I n d k) :
    ∃ r : R, IsNilpotent (y - algebraMap R _ r) := by
  obtain ⟨g, rfl⟩ := nv_surj k y
  obtain ⟨⟨ψ, hψ, hC, -⟩, h0, -⟩ := nv_calculus R _ (algebraMap R _) n d _ (lev_xK (I := I) k).nil
  refine ⟨MvPowerSeries.constantCoeff g, ?_⟩
  have := (h0 (g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) (by simp)).1
  rwa [← hψ, map_sub, hC, hψ] at this

end

theorem exists_series_of_natural : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  intro R _ I hI n d L hL c hc
  choose g hg using fun k => nv_surj k (c (MainNotions I n d k) (xK I n d k))
  have key : ∀ (k : ℕ) (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S →
      Lev I k S a → c S a = nv (algebraMap R S) (g k) a := by
    intro k S _ _ a hS ha
    obtain ⟨φ, hφ⟩ := exists_lift ha
    have h1 := hc _ S φ (xK I n d k) (hL k k) hS (const_add_nil k) ⟨k, (lev_xK k).1⟩ (lev_xK k).nil
    rw [← hg, nv_lift φ (lev_xK k).nil] at h1
    simp only [hφ] at h1
    exact h1.symm
  have hcomp : IsAdicComplete (JJ I n d) (PS R n d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete R I (Fin n × Fin d)).2 hI
  obtain ⟨f, hf⟩ := hcomp.toIsPrecomplete.prec (f := g) fun {k k'} h => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    refine Ideal.pow_le_pow_right (Nat.le_succ k) (mem_of_nv_eq k _ _ ?_)
    rw [← key k _ _ (hL k k) (lev_xK k), ← key k' _ _ (hL k k) ((lev_xK k).mono h)]
  refine ⟨f, fun S _ _ a hS hk ha => ?_⟩
  obtain ⟨k, hk⟩ := exists_lev hk ha
  obtain ⟨ψ, hψ, hC, hX⟩ := (nv_calculus R _ (algebraMap R S) n d _ ha).1
  have h1 := hf (k + 1 + (k + 1))
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hom_kill hk ψ hC hX _ h1
  rw [map_sub, sub_eq_zero, hψ, hψ] at h2
  rw [key (k + 1 + (k + 1)) S a hS (hk.mono (by omega)), h2]

end GlobalTheory.ChF
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  first | exact @GlobalTheory.ChF.changeCoeff_law_lin_extSer | exact GlobalTheory.ChF.changeCoeff_law_lin_extSer | (intros; apply GlobalTheory.ChF.changeCoeff_law_lin_extSer <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  first | exact @GlobalTheory.FormalPts.points_addCommMonoid | exact GlobalTheory.FormalPts.points_addCommMonoid | (intros; apply GlobalTheory.FormalPts.points_addCommMonoid <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by
  first | exact @GlobalTheory.ChF.eq_of_nv_eq | exact GlobalTheory.ChF.eq_of_nv_eq | (intros; apply GlobalTheory.ChF.eq_of_nv_eq <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ c, WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (t c)) := by
  first | exact @GlobalTheory.LeafCoordWeight.weight_nonneg | exact GlobalTheory.LeafCoordWeight.weight_nonneg | (intros; apply GlobalTheory.LeafCoordWeight.weight_nonneg <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.zetaSeries_leaf_mainTerm_curveSystem : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z I) (a : ZMod d) (i : ℕ), Adapted S D a i → i < d → ∀ t : I → MvPowerSeries I C, S.IsT t → ∀ (N : ℕ) (em : Fin N → I), (∀ δ, D.lev (em δ) = 0) → ∀ κ : J, G.ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull (fun δ => S.tan (em δ)) (S.ze t κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, mainVec S D (em δ) κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
  first | exact @GlobalTheory.MainTerm.zeta_leaf_main_term | exact GlobalTheory.MainTerm.zeta_leaf_main_term | (intros; apply GlobalTheory.MainTerm.zeta_leaf_main_term <;> assumption)
end
