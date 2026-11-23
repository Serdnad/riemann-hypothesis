module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle103
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle010
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle968
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatEnt

def QSum {G : Type} [CommGroup G] (H : Subgroup G) (F : G → ℂ) (a : ℂ) : Prop :=
  HasSum (fun q : G ⧸ H => F q.out) a

section Generic

variable {G : Type} [CommGroup G] {H H' : Subgroup G} {F : G → ℂ} {a : ℂ}

theorem out_mk (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (g : G) : F (QuotientGroup.mk g : G ⧸ H).out = F g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hu, hF _ _ u.2]

theorem QSum.translate (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) (t : G) :
    QSum H (fun g => F (t * g)) a := by
  unfold QSum at *
  rw [← (Equiv.mulLeft (QuotientGroup.mk t : G ⧸ H)).hasSum_iff] at h
  refine h.congr_fun fun q => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : ∀ g, ∀ u ∈ H, F (t * (g * u)) = F (t * g) := fun g u hu => by rw [← mul_assoc, hF _ _ hu]
  exact (out_mk (F := fun g => F (t * g)) h2 g).trans (out_mk hF (t * g)).symm

theorem QSum.eq_zero (hF : ∀ g, ∀ u ∈ H, F (g * u) = F g) (h : QSum H F a) {t : G} {c : ℂ} (hc : c ≠ 1)
    (ht : ∀ g, F (t * g) = c * F g) : a = 0 := by
  have h1 := h.translate hF t
  unfold QSum at *
  simp only [ht] at h1
  have h2 := h1.unique (h.mul_left c)
  have : (c - 1) * a = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)

theorem qsum_index (hle : H ≤ H') (hn : H.relIndex H' ≠ 0) (hF : ∀ g, ∀ u ∈ H', F (g * u) = F g) :
    QSum H' F a ↔ QSum H F (H.relIndex H' * a) := by
  unfold QSum
  haveI : (H.subgroupOf H').FiniteIndex := ⟨hn⟩
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  have hc : (Fintype.card (H' ⧸ H.subgroupOf H') : ℂ) = H.relIndex H' := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  have hn' : (H.relIndex H' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  let e := Subgroup.quotientEquivProdOfLE hle
  have he : ∀ q : G ⧸ H, F q.out = (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q) := fun q => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [out_mk fun g u hu => hF g u (hle hu)]
    show _ = F (QuotientGroup.mk g : G ⧸ H').out * 1
    rw [out_mk hF, mul_one]
  simp only [he]
  rw [show (fun q => (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) (e q)) =
    (fun p : (G ⧸ H') × (H' ⧸ H.subgroupOf H') => F p.1.out * 1) ∘ e from rfl, e.hasSum_iff]
  have h1 : HasSum (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) (H.relIndex H') := by
    simpa [hc] using hasSum_fintype (fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ))
  constructor
  · intro h
    rw [mul_comm]
    have h3 := summable_mul_of_summable_norm (f := fun q : G ⧸ H' => F q.out)
      (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h.summable.norm h1.summable.norm
    exact HasSum.mul (f := fun q : G ⧸ H' => F q.out) (g := fun _ : H' ⧸ H.subgroupOf H' => (1 : ℂ)) h h1 h3
  · intro h
    have h2 := (h.prod_fiberwise fun q => h1.mul_left (F q.out)).mul_right (H.relIndex H' : ℂ)⁻¹
    simp only [mul_assoc, mul_inv_cancel₀ hn', mul_one] at h2
    rwa [mul_left_comm, mul_inv_cancel₀ hn', mul_one] at h2

end Generic

variable {E : Type} [Field E] [NumberField E]

def box (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Set (Af E)ˣ :=
  {z | ∀ w, Valued.v ((z : Af E) w - 1) ≤ r w}

def congr (r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)) : Subgroup (Af E)ˣ where
  carrier := {z | ∀ w, Valued.v ((z : Af E) w) = 1 ∧ Valued.v ((z : Af E) w - 1) ≤ r w}
  one_mem' := fun w => by
    have : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl
    rw [this]; simp
  mul_mem' := fun {a b} ha hb w => by
    have : ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl
    rw [this]
    refine ⟨by rw [map_mul, (ha w).1, (hb w).1, one_mul], ?_⟩
    rw [show (a : Af E) w * (b : Af E) w - 1 = (a : Af E) w * ((b : Af E) w - 1) + ((a : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (ha w).1, one_mul]; exact (hb w).2) (ha w).2
  inv_mem' := fun {a} ha w => by
    have h : (a : Af E) w * ((a⁻¹ : (Af E)ˣ) : Af E) w = 1 := (coord w a).val_inv
    have h1 : Valued.v (((a⁻¹ : (Af E)ˣ) : Af E) w) = 1 := by
      have := congrArg Valued.v h
      rwa [map_mul, (ha w).1, one_mul, map_one] at this
    refine ⟨h1, ?_⟩
    rw [show ((a⁻¹ : (Af E)ˣ) : Af E) w - 1 = -(((a⁻¹ : (Af E)ˣ) : Af E) w * ((a : Af E) w - 1)) by
      linear_combination h, Valuation.map_neg, map_mul, h1, one_mul]
    exact (ha w).2

def radN (E : Type) [Field E] [NumberField E] (N : ℕ) (w : HeightOneSpectrum (𝓞 E)) : WithZero (Multiplicative ℤ) :=
  Valued.v (N : w.adicCompletion E)

def zterm (χ : HChar E) (s : ℂ) (z : (Af E)ˣ) : ℂ := (finPart χ z : ℂ) * ((modF z : ℝ) : ℂ) ^ s

theorem zterm_mul (χ : HChar E) (s : ℂ) (z z' : (Af E)ˣ) : zterm χ s (z * z') = zterm χ s z * zterm χ s z' := by
  unfold zterm
  rw [map_mul, ObjModel.modF_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ObjModel.modF_pos _).le (ObjModel.modF_pos _).le, Units.val_mul]
  ring

theorem differentiable_zterm (χ : HChar E) (z : (Af E)ˣ) : Differentiable ℂ fun s => zterm χ s z :=
  Differentiable.const_mul (Differentiable.const_cpow differentiable_id
    (Or.inl (by exact_mod_cast (ObjModel.modF_pos z).ne'))) _

theorem modF_eq_one {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) : modF u = 1 := by
  unfold modF
  exact finprod_eq_one_of_forall_eq_one fun v => by simp [hu v]

theorem zterm_unit (χ : HChar E) (s : ℂ) {u : (Af E)ˣ} (hu : ∀ w, Valued.v ((u : Af E) w) = 1) :
    zterm χ s u = finPart χ u := by
  simp [zterm, modF_eq_one hu]

theorem norm_zterm {χ : HChar E} (h : IsUnitary χ) (s : ℂ) (z : (Af E)ˣ) : ‖zterm χ s z‖ = modF z ^ s.re := by
  have : ‖(finPart χ z : ℂ)‖ = 1 := h _
  rw [zterm, norm_mul, this, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ObjModel.modF_pos z)]

theorem mul_mem_box {r : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} {z u : (Af E)ˣ} (hu : u ∈ congr r) :
    z * u ∈ box r ↔ z ∈ box r := by
  have key : ∀ z u : (Af E)ˣ, u ∈ congr r → z ∈ box r → z * u ∈ box r := fun z u hu hz w => by
    have : ((z * u : (Af E)ˣ) : Af E) w = (z : Af E) w * (u : Af E) w := rfl
    rw [this, show (z : Af E) w * (u : Af E) w - 1 = (u : Af E) w * ((z : Af E) w - 1) + ((u : Af E) w - 1) by ring]
    exact Valuation.map_add_le _ (by rw [map_mul, (hu w).1, one_mul]; exact hz w) (hu w).2
  exact ⟨fun h => by simpa using key _ _ (inv_mem hu) h, key _ _ hu⟩

theorem congr_mono {r r' : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ)} (h : ∀ w, r w ≤ r' w) :
    congr r ≤ congr r' := fun _ hz w => ⟨(hz w).1, (hz w).2.trans (h w)⟩

theorem mem_hatO_of_sub {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) {a z : Af E} (ha : a ∈ hatO c)
    (hz : ∀ P, Valued.v (z P - a P) ≤ radN E n P) : z ∈ hatO c := by
  have hn0 : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have key := GlobalTheory.IntDense.mem_of_isClosed E (C := {α | algebraMap E (Af E) n * α ∈ hatO c})
    ((Subring.isClosed_topologicalClosure _).preimage (continuous_const.mul continuous_id)) (fun a => by
      show _ ∈ hatO c
      rw [← map_mul]
      refine algebraMap_mem_hatO (mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) n * a,
        Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩)
      simp) (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) fun P => by
      have h0 := GlobalTheory.AdLat.valued_natCast_ne_zero P hn
      show Valued.v (algebraMap E (P.adicCompletion E) (n : E)⁻¹ * (z P - a P)) ≤ 1
      rw [map_mul, map_inv₀, map_inv₀, map_natCast, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
      exact hz P
  have e : z = algebraMap E (Af E) n * (algebraMap E (Af E) (n : E)⁻¹ * (z - a)) + a := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul, sub_add_cancel]
  rw [e]
  exact add_mem key ha

theorem congr_le_hatOUnits {c : Ideal (OF E)} {n : ℕ} (hn : 0 < n) (hc : (n : OF E) ∈ c) :
    congr (radN E n) ≤ hatOUnits c := fun _ hu =>
  mem_hatOUnits.2 ⟨mem_hatO_of_sub hn hc (one_mem _) fun P => (hu P).2,
    mem_hatO_of_sub hn hc (one_mem _) fun P => (inv_mem hu P).2⟩

theorem hatOUnits_le_congr (c : Ideal (OF E)) : hatOUnits c ≤ congr (fun _ => 1) := fun u hu w => by
  have h : Valued.v ((u : Af E) w) = 1 :=
    GlobalTheory.Mem.TupHecke.valued_eq_one_of_le (coord w u) (ObjModel.hatO_integral hu.1 w) (ObjModel.hatO_integral hu.2 w)
  exact ⟨h, Valuation.map_sub_le _ h.le (by simp)⟩

end GlobalTheory.CMVal.LatEnt
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Conv

variable {E : Type} [Field E] [NumberField E]

theorem mem_integers_of_mem_hatO {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    y v ∈ v.adicCompletionIntegers E := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  refine closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
    rw [map_add (f := _)]; rfl
  rw [this]
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)

theorem exists_denominator (c : Ideal (OF E)) (y : (Af E)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ lattice c y, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * x := by
  obtain ⟨n, hn, hy⟩ := PI.AdCpctDenWork.exists_nat_adele (y : Af E)
  refine ⟨n, hn, fun x hx => ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
  have h1 := mul_mem (hy v) (mem_integers_of_mem_hatO hx v)
  have h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x) := by
    rw [map_mul, map_natCast]
    linear_combination ((n : Af E) * algebraMap E (Af E) x) * y.mul_inv
  have h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E := by
    rw [← h2]; exact h1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)


omit [NumberField E] in
theorem exists_generator : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by
  classical
  refine ⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩
  have h : ∃ b', Ideal.span {b'} = Ideal.span {b} := ⟨b, rfl⟩
  simp only [dif_pos h]
  exact Ideal.span_singleton_eq_span_singleton.1 h.choose_spec

theorem summable_norm_rpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by
  intro E _ _ _ c y t _ ht
  obtain ⟨n, hn, hL⟩ := exists_denominator c y
  choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1
  obtain ⟨g, hg⟩ := exists_generator (E := E)
  choose u hu using hg
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  let f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E) :=
    fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})
  have hf : Function.Injective f := by
    intro q q' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E := by
      rw [← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E _).1 h3
    have h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q := by
      rw [hv]
      have e1 := hu (b q)
      have e2 := hu (b q')
      rw [← h2] at e2
      rw [Units.val_mul]
      linear_combination (-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1
        - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv
    have h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out := by
      apply mul_left_cancel₀ hn'
      rw [← hb q', h4, map_mul, hb q, mul_left_comm]; rfl
    apply Subtype.ext
    rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
    exact Quotient.sound ⟨v, h5⟩
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1
  have hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t) := by
    refine (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩
    exact Summable.of_finite
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hn')
  refine ((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_
  have h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) =
      |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs,
      ← Algebra.coe_norm_int]
    simp
  show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _
  rw [h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]
  simp

end GlobalTheory.CMVal.Conv
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.LiftBasis

theorem exists_lift_isAdapted : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → ∀ (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → ∃ e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q, (∀ l, map Θ (e l) = e0 l) ∧ IsBasis μ' e ∧ IsAdapted F.θ μ' e := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hμ' hμ Θ hΘ k e0 hB hA
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have hF : IsFrame p F.Q F.θ := F.frame
  have hμf : (fun i => map F.θ (μ' i)) = c.μ := funext hμ

  have hw : ∀ l, ∃ w : Fin d → F.B, (∀ i, lin (e0 l) i = algebraMap O C (F.θ (w i))) ∧
      ∀ j, l = Sum.inl j → w = Pi.single j 1 := by
    intro l
    cases l with
    | inl j =>
      refine ⟨Pi.single j 1, fun i => ?_, fun j' h => by cases h; rfl⟩
      rw [(hA j).2]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    | inr j =>
      refine ⟨fun i => Classical.choose (hF.surj (Classical.choose ((hB.1 (Sum.inr j)).2.1 i))),
        fun i => ?_, fun j' h => by cases h⟩
      rw [Classical.choose_spec (hF.surj _)]
      exact (Classical.choose_spec ((hB.1 (Sum.inr j)).2.1 i)).2
  choose w hw1 hw2 using hw
  have hlift : ∀ l, ∃ f : MvPowerSeries (Fin d) F.Q, QL μ' ⊤ f ∧ map Θ f = e0 l ∧
      ∀ i, lin f i = algebraMap F.B F.Q (w l i) := by
    intro l
    refine GlobalTheory.T.lift_quasiLogarithm_along_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (e0 l) (w l) ?_ (hw1 l)
    rw [hμf]; exact hB.1 l
  choose e he1 he2 he3 using hlift
  refine ⟨e, he2, ?_, ?_⟩
  · refine GlobalTheory.T.quasiLogarithm_basis_lift_pdThickening p F.B O F.Q F.θ hF d μ' hμ' C hC Θ hΘ (Fin d ⊕ Fin k) e he1 ?_
      (GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain p C v O hv ε hε F)
    rw [hμf]
    have : (fun i => map Θ (e i)) = e0 := funext he2
    rw [this]; exact hB
  · intro i
    refine ⟨fun α => ?_, ?_⟩
    · obtain ⟨b, -, eb⟩ := (he1 (Sum.inl i)).2.2 α
      refine ⟨b, RingHom.mem_ker.2 ?_, eb⟩
      obtain ⟨b', hb', eb'⟩ := (hA i).1 α
      have hb0 : b' = 0 := RingHom.mem_ker.1 hb'
      have hup : up C c.μ = fun j => map Θ (up F.Q μ' j) :=
        funext (WindowMat.up_map F.θ Θ hΘ hμ)
      have key : algebraMap O C (F.θ b) = 0 := by
        rw [← hΘ, ← eb, ← coeff_map, Window.map_formalGroupLawCoboundaryOne_eq Θ _ (Window.constantCoeff_up hμ'.const),
          ← hup, he2, eb', hb0, map_zero]
      exact hC.inj (by rw [key, map_zero])
    · funext j
      rw [he3, hw2 _ i rfl]
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]

end GlobalTheory.QLog.LiftBasis
end
end

section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

namespace DefectSurj

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_const {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) : ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem powerSeriesPullbackTwoGroups_add_smul {φ : Fin d → MvPowerSeries (Fin d) R} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (a : R) (κ h : MvPowerSeries (Fin d ⊕ Fin d) R) :
    pull2 φ (κ + a • h) = pull2 φ κ + a • pull2 φ h := by
  have hs : HasSubst (Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))) := by
    refine hasSubst_of_constantCoeff_zero ?_
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
  unfold pull2 at2
  rw [subst_add hs, subst_smul hs]

end DefectSurj

theorem additive_mod_p_is_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  intro p _ O E _ _ _ hF G d c b z hb
  obtain ⟨κ, B, y, h0, h2, hsw, hB, hev⟩ := GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p p O G d c (-b) (-z)
    (by rw [map_neg, hb, smul_neg])
  obtain ⟨f, hf, -, hin⟩ := GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog p O E hF d c.μ c.isLaw (p : O) dvd_rfl κ h0 h2 hsw
  obtain ⟨t, ht, hmt⟩ := (GlobalTheory.series_in_ideal_iff_image O E _ _ _).1.1 hin
  obtain ⟨h, rfl⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) t).1
    (fun α => Ideal.mem_span_singleton.1 (ht α))
  have hκ : map (algebraMap O E) (κ + (p : O) • h) = cob1 (up E c.μ) f := by
    rw [map_add (f := _), hmt]; abel
  obtain ⟨s, hs, -⟩ := (GlobalTheory.T.defect_ev_succ_eq_mulP_add_p_pow_smul p O E hF G d c f hf).1 p
  have hc := ((GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f _ hκ).2.2 p s hs).1
  rw [DefectSurj.powerSeriesPullbackTwoGroups_add_smul (DefectSurj.nmul_const c.isLaw.const p)] at hc
  obtain ⟨u, hu⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1 hB
  have hsum : cob1 c.μ (s + B) =
      (p : O) • (κ + (p : O) • h - pull2 (nmul c.μ p) h + u) := by
    rw [formalCoboundary_add c.isLaw.const, hc, smul_add _ _ u, smul_sub, ← hu]; abel
  have hdiv := GlobalTheory.T.coeff_mem_of_coeff_cob1_mem p O G d c (Ideal.span {(p : O)}) (Ideal.mem_span_singleton_self _)
    (s + B) (fun α => Ideal.mem_span_singleton.2
      (((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).2 ⟨_, hsum⟩ α))
  obtain ⟨w, hw⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1
    (fun α => Ideal.mem_span_singleton.1 (hdiv α))
  refine ⟨f, s, c.ev 1 w - y, hf, hs, ?_⟩
  have := congrArg (c.ev 1) hw
  rw [map_add (f := _), map_smul, hev] at this
  rw [smul_sub, ← this]; abel

end GlobalTheory.QLog
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_smoothLift_of_retract_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.retractLift | exact GlobalTheory.Obs.retractLift | (intros; apply GlobalTheory.Obs.retractLift <;> assumption)
end
