module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem dxi_zero' (A : PAlg l) (n : ℕ) : A.dxi n 0 = 1 := by
  show A.mkAcr n (A.dxi0 0) = 1
  rw [← map_one (A.mkAcr n)]
  congr 1
  apply Subtype.ext
  simp [PAlg.dxi0, dpw]

theorem fil_zero' (A : PAlg l) (n : ℕ) : A.Fil n 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (dxi_zero' A n ▸ Ideal.subset_span ⟨0, le_rfl, rfl⟩)

theorem fil_succ_le' (A : PAlg l) (n r : ℕ) : A.Fil n (r + 1) ≤ A.Fil n r :=
  Ideal.span_mono fun _ ⟨k, hk, hz⟩ => ⟨k, by omega, hz⟩

theorem dxi_mem_fil' (A : PAlg l) (n r : ℕ) : A.dxi n r ∈ A.Fil n r := Ideal.subset_span ⟨r, le_rfl, rfl⟩

def gr (h : RGr l) (A : PAlg l) (n r : ℕ) (z : A.Acr n) (hz : z ∈ A.Fil n r) : A.Un n :=
  Ideal.Quotient.mk _ (A.th (Classical.choose ((h A n r).1 z hz)))

theorem gr_eq (h : RGr l) (A : PAlg l) {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) (x : A.W)
    (hx : z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) : gr h A n r z hz = Ideal.Quotient.mk _ (A.th x) := by
  have h0 := Classical.choose_spec ((h A n r).1 z hz)
  show Ideal.Quotient.mk _ (A.th (Classical.choose ((h A n r).1 z hz))) = _
  rw [Ideal.Quotient.eq, ← map_sub]
  apply ((h A n r).2 _).1
  have e : A.toAcr n (Classical.choose ((h A n r).1 z hz) - x) * A.dxi n r =
      (z - A.toAcr n x * A.dxi n r) - (z - A.toAcr n (Classical.choose ((h A n r).1 z hz)) * A.dxi n r) := by
    rw [map_sub]; ring
  rw [e]; exact sub_mem hx h0

theorem gr_spec (h : RGr l) (A : PAlg l) {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) :
    ∃ x : A.W, z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1) ∧ gr h A n r z hz = Ideal.Quotient.mk _ (A.th x) :=
  ⟨_, Classical.choose_spec ((h A n r).1 z hz), rfl⟩

def fv {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : A.Acr n := z.1

theorem fv_mem {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : fv z ∈ A.Fil n r := z.2

theorem fv_add {A : PAlg l} {n r : ℕ} (z z' : (FilF l n r).obj A) : fv (z + z') = fv z + fv z' := rfl

theorem fv_zero {A : PAlg l} {n r : ℕ} : fv (0 : (FilF l n r).obj A) = 0 := rfl

theorem gr_zero (h : RGr l) (A : PAlg l) (n r : ℕ) : gr h A n r (fv (0 : (FilF l n r).obj A)) (fv_mem _) = 0 := by
  rw [gr_eq h A _ _ 0 (by rw [fv_zero, map_zero, zero_mul, sub_zero]; exact zero_mem _), map_zero, map_zero]

theorem gr_add (h : RGr l) (A : PAlg l) (n r : ℕ) (z z' : (FilF l n r).obj A) :
    gr h A n r (fv (z + z')) (fv_mem _) = gr h A n r (fv z) (fv_mem z) + gr h A n r (fv z') (fv_mem z') := by
  obtain ⟨x, hx, e⟩ := gr_spec h A (fv z) (fv_mem z)
  obtain ⟨x', hx', e'⟩ := gr_spec h A (fv z') (fv_mem z')
  have hs : fv (z + z') - A.toAcr n (x + x') * A.dxi n r =
      (fv z - A.toAcr n x * A.dxi n r) + (fv z' - A.toAcr n x' * A.dxi n r) := by rw [fv_add, map_add (f := _)]; ring
  rw [gr_eq h A _ _ (x + x') (by rw [hs]; exact add_mem hx hx'), e, e', map_add (f := _), map_add (f := _)]

def grF (h : RGr l) (A : PAlg l) (n r : ℕ) : (FilF l n r).obj A →+ (UnF l n).obj A where
  toFun z := gr h A n r (fv z) (fv_mem z)
  map_zero' := gr_zero h A n r
  map_add' := gr_add h A n r

theorem grF_apply (h : RGr l) (A : PAlg l) {n r : ℕ} (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) : grF h A n r z = Ideal.Quotient.mk _ (A.th x) :=
  gr_eq h A _ (fv_mem z) x hx

theorem fv_inj {A : PAlg l} {n r : ℕ} {z z' : (FilF l n r).obj A} (e : fv z = fv z') : z = z' := Subtype.ext e

def mkF {A : PAlg l} {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) : (FilF l n r).obj A := ⟨z, hz⟩

theorem fv_mkF {A : PAlg l} {n r : ℕ} (z : A.Acr n) (hz : z ∈ A.Fil n r) : fv (mkF (l := l) z hz) = z := rfl

theorem fv_smul {A : PAlg l} {n r : ℕ} (a : Acris l) (z : (FilF l n r).obj A) : fv (a • z) = A.cris n a * fv z := rfl

theorem fv_map {A B : PAlg l} (f : A ⟶ B) {n r : ℕ} (z : (FilF l n r).obj A) :
    fv (((FilF l n r).map f).hom z) = mapAcr f n (fv z) := rfl

theorem un_smul (A : PAlg l) (n : ℕ) (a : Ainf l) (x : A.W) :
    (a • (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th x))) =
      (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th (A.sW a * x))) := rfl

theorem un_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (x : A.W) :
    ((UnF l n).map f).hom (Ideal.Quotient.mk _ (A.th x)) = Ideal.Quotient.mk _ (B.th (mapW f x)) := rfl

def grx (h : RGr l) {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) : A.W := Classical.choose ((h A n r).1 (fv z) (fv_mem z))

theorem grx_spec (h : RGr l) {A : PAlg l} {n r : ℕ} (z : (FilF l n r).obj A) :
    fv z - A.toAcr n (grx h z) * A.dxi n r ∈ A.Fil n (r + 1) := Classical.choose_spec ((h A n r).1 (fv z) (fv_mem z))

theorem un_smul' (A : PAlg l) (n : ℕ) (a : Ainf l) (x : A.W) :
    (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th (A.sW a * x))) = RingHom.id (Ainf l) a • (show (UnF l n).obj A from Ideal.Quotient.mk _ (A.th x)) := by
  rw [RingHom.id_apply]; exact (un_smul A n a x).symm

theorem grF_algebraMap_smul (h : RGr l) (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) (x : A.W) (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1))
    (hm : fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r ∈ A.Fil n (r + 1)) :
    grF h A n r (algebraMap (Ainf l) (Acris l) a • z) = RingHom.id (Ainf l) a • grF h A n r z := by
  rw [grF_apply h A _ _ hm, grF_apply h A z x hx]
  exact un_smul' A n a x

theorem smul_mem_filtration_graded (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) (x : A.W) (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r ∈ A.Fil n (r + 1) := by
  have : fv (algebraMap (Ainf l) (Acris l) a • z) - A.toAcr n (A.sW a * x) * A.dxi n r =
      A.toAcr n (A.sW a) * (fv z - A.toAcr n x * A.dxi n r) := by
    rw [fv_smul, cris_algebraMap, map_mul]; ring
  rw [this]; exact Ideal.mul_mem_left _ _ hx

theorem grF_smul (h : RGr l) (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n r).obj A) :
    grF h A n r (algebraMap (Ainf l) (Acris l) a • z) = RingHom.id (Ainf l) a • grF h A n r z :=
  grF_algebraMap_smul h A n r a z _ (grx_spec h z) (smul_mem_filtration_graded A n r a z _ (grx_spec h z))

def incF (A : PAlg l) (n r : ℕ) : (FilF l n (r + 1)).obj A →+ (FilF l n r).obj A where
  toFun z := mkF (fv z) (fil_succ_le' A n r (fv_mem z))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fv_incF (A : PAlg l) (n r : ℕ) (z : (FilF l n (r + 1)).obj A) : fv (incF A n r z) = fv z := rfl

theorem incF_inj (A : PAlg l) (n r : ℕ) : Function.Injective (incF A n r) := fun z z' e => fv_inj (by
  have := congrArg (fv (l := l) (A := A) (n := n) (r := r)) e
  rwa [fv_incF, fv_incF] at this)

theorem incF_smul (A : PAlg l) (n r : ℕ) (a : Ainf l) (z : (FilF l n (r + 1)).obj A) :
    incF A n r (algebraMap (Ainf l) (Acris l) a • z) = algebraMap (Ainf l) (Acris l) a • incF A n r z := rfl

theorem incF_nat {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n (r + 1)).obj A) :
    incF B n r (((FilF l n (r + 1)).map f).hom z) = ((FilF l n r).map f).hom (incF A n r z) := rfl

theorem ex_mem (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) (x : A.W)
    (hx : fv y - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) (h0 : (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ n}) (A.th x) : A.Un n) = 0) :
    fv y ∈ A.Fil n (r + 1) := by
  have hm := ((h A n r).2 x).2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have : fv y = (fv y - A.toAcr n x * A.dxi n r) + A.toAcr n x * A.dxi n r := by ring
  rw [this]; exact add_mem hx hm

theorem ex1 (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) (x : A.W)
    (hx : fv y - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) (hy : grF h A n r y = 0) : y ∈ Set.range (incF A n r) :=
  ⟨mkF (fv y) (ex_mem h A n r y x hx ((grF_apply h A y x hx).symm.trans hy)), fv_inj (fv_incF A n r _)⟩

theorem ex2 (h : RGr l) (A : PAlg l) (n r : ℕ) (w : (FilF l n (r + 1)).obj A) : grF h A n r (incF A n r w) = 0 := by
  rw [grF_apply h A _ 0 (by rw [fv_incF, map_zero, zero_mul, sub_zero]; exact fv_mem w), map_zero, map_zero]

theorem ex3 (h : RGr l) (A : PAlg l) (n r : ℕ) (y : (FilF l n r).obj A) : grF h A n r y = 0 ↔ y ∈ Set.range (incF A n r) := by
  constructor
  · exact ex1 h A n r y _ (grx_spec h y)
  · rintro ⟨w, rfl⟩
    exact ex2 h A n r w

theorem grF_exact (h : RGr l) (A : PAlg l) (n r : ℕ) : Function.Exact (incF A n r) (grF h A n r) := by
  intro y
  exact ex3 h A n r y

theorem grF_surj (h : RGr l) (A : PAlg l) (n r : ℕ) : Function.Surjective (grF h A n r) := by
  intro u
  obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(l : A.U) ^ n}) u
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u'
  refine ⟨mkF (A.toAcr n x * A.dxi n r) (Ideal.mul_mem_left _ _ (dxi_mem_fil' A n r)), ?_⟩
  exact grF_apply h A _ x (by rw [fv_mkF, sub_self]; exact zero_mem _)

theorem nat_mem {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    fv (((FilF l n r).map f).hom z) - B.toAcr n (mapW f x) * B.dxi n r ∈ B.Fil n (r + 1) := by
  rw [fv_map, ← mapAcr_toAcr, ← mapAcr_dxi f n r, ← map_mul, ← map_sub]
  exact mapAcr_fil f n (r + 1) hx

theorem graded_naturality (h : RGr l) {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) (x : A.W)
    (hx : fv z - A.toAcr n x * A.dxi n r ∈ A.Fil n (r + 1)) :
    grF h B n r (((FilF l n r).map f).hom z) = ((UnF l n).map f).hom (grF h A n r z) := by
  rw [grF_apply h B _ _ (nat_mem f n r z x hx), grF_apply h A z x hx]
  exact (un_map f n x).symm

theorem grF_nat (h : RGr l) {A B : PAlg l} (f : A ⟶ B) (n r : ℕ) (z : (FilF l n r).obj A) :
    grF h B n r (((FilF l n r).map f).hom z) = ((UnF l n).map f).hom (grF h A n r z) :=
  graded_naturality h f n r z _ (grx_spec h z)

def fil0Inclusion (A : PAlg l) (n : ℕ) : (FilF l n 0).obj A →+ (AcrF l n).obj A where
  toFun z := fv z
  map_zero' := rfl
  map_add' _ _ := rfl

theorem filtration_zero_inclusion_bijective (A : PAlg l) (n : ℕ) : Function.Bijective (fil0Inclusion A n) :=
  ⟨fun _ _ e => fv_inj e, fun y => ⟨mkF (r := 0) y (by rw [fil_zero']; trivial), rfl⟩⟩

theorem filtration_zero_inclusion_smul (A : PAlg l) (n : ℕ) (a : Acris l) (z : (FilF l n 0).obj A) :
    fil0Inclusion A n (a • z) = RingHom.id (Acris l) a • fil0Inclusion A n z := rfl

theorem fil0Inclusion_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (z : (FilF l n 0).obj A) :
    fil0Inclusion B n (((FilF l n 0).map f).hom z) = ((AcrF l n).map f).hom (fil0Inclusion A n z) := rfl

end CrystallineSemistableComparison.D
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem flagDomainConj_hostXi_eq_neg : WittVector.constantCoeff (xi0 l) = -pFlat l := by
  rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
  exact congrArg Neg.neg (WittVector.teichmuller_coeff_zero l _)

theorem un_rep {A : PAlg l} {n : ℕ} (x : A.Un n) : ∃ w : A.W, x = Ideal.Quotient.mk _ (A.th w) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u
  exact ⟨w, rfl⟩

variable (A : PAlg l)

def rho0 : A.U →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : WittVector.constantCoeff A.xi = -A.pi := by
      change (WittVector.map A.s (xi0 l)).coeff 0 = -A.s (pFlat l)
      rw [WittVector.map_coeff, ← map_neg, ← flagDomainConj_hostXi_eq_neg]; rfl
    rw [RingHom.comp_apply, map_mul, e]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _)))

def rho : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ (rho0 A) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {A.pi})), A.natCast_l, map_zero,
      zero_pow one_ne_zero, mul_zero]

theorem rho_mk (w : A.W) : rho A (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (w.coeff 0) := rfl

theorem rho_bij (hU : RU l) : Function.Bijective (rho A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := un_rep x
    rw [rho_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have := ((hU A).2 w).2 hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [pow_one])
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (A.th (WittVector.teichmuller l a)), by rw [rho_mk, WittVector.teichmuller_coeff_zero]⟩

theorem span_pi_eq : (Ideal.span {A.pi}).restrictScalars (Ob l) = (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, trivial, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]; rfl⟩

def kappa : (A.A ⧸ Ideal.span {A.pi}) ≃ₗ[Ob l] A.A ⧸ (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) :=
  (Submodule.Quotient.restrictScalarsEquiv (Ob l) (Ideal.span {A.pi})).symm.trans (Submodule.quotEquivOfEq _ _ (span_pi_eq A))

def tau1 : A.Un 1 →+ (Ob l ⧸ Ideal.span {pFlat l}) ⊗[Ob l] A.A :=
  ((TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.toAddMonoidHom.comp
    (kappa A).toAddMonoidHom).comp (rho A).toAddMonoidHom

theorem kappa_mk (x : A.A) :
    kappa A (Ideal.Quotient.mk _ x) = Submodule.Quotient.mk (p := (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A)) x := by
  rfl

theorem tau1_mk (w : A.W) : tau1 A (Ideal.Quotient.mk _ (A.th w)) = (1 : Ob l ⧸ Ideal.span {pFlat l}) ⊗ₜ[Ob l] w.coeff 0 := by
  change (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm (kappa A (rho A (Ideal.Quotient.mk _ (A.th w)))) = _
  rw [rho_mk, kappa_mk]
  exact TensorProduct.quotTensorEquivQuotSMul_symm_mk _ _

theorem tau1_bijective (hU : RU l) : Function.Bijective (tau1 A) :=
  (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.bijective.comp
    ((kappa A).bijective.comp (rho_bij A hU))

theorem tau1_smul (a : Ainf l) (x : A.Un 1) :
    tau1 A (a • x) = WittVector.constantCoeff a • tau1 A x := by
  obtain ⟨w, rfl⟩ := un_rep x
  have e : a • (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th w)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th (A.sW a * w)) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (Ainf l) A.U, Ideal.Quotient.algebraMap_eq, ← map_mul, map_mul A.th]; rfl
  rw [e, tau1_mk, tau1_mk, ← TensorProduct.tmul_smul, WittVector.mul_coeff_zero, Algebra.smul_def]
  change _ ⊗ₜ[Ob l] ((WittVector.map A.s a).coeff 0 * _) = _
  rw [WittVector.map_coeff]; rfl

end CrystallineSemistableComparison.D
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

abbrev pfOb {R : Type} [CommRing R] {p : ℕ} (X : Type) [CommRing X] [Algebra R X] (h : Pf p X) : PfC p R :=
  ⟨CommAlgCat.of R X, h⟩

abbrev pfHom {R : Type} [CommRing R] {p : ℕ} {X Y : Type} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    {hX : Pf p X} {hY : Pf p Y} (φ : X →ₐ[R] Y) : pfOb (R := R) X hX ⟶ pfOb (R := R) Y hY :=
  ObjectProperty.homMk (CommAlgCat.ofHom φ)

abbrev pfFrom {R : Type} [CommRing R] {p : ℕ} (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B]
    [IsScalarTower R A.obj B] (hB : Pf p B) : A ⟶ pfOb (R := R) B hB :=
  ObjectProperty.homMk (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A.obj B))

end CrystallineSemistableComparison.D
end
end
