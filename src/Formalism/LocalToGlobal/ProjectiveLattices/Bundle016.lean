module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle004

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj.FrCov

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

section Comb

variable {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
  {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}

theorem eps_dual (ψ : S →+* T) (a : S) : spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

end Comb

variable (hS' : Out.SecBaseChangeAnySt) (hT : Out.SecTwistSt) {R T T' : Type} [CommRing R] [Algebra c.F R] [CommRing T]
  [Algebra c.F T] [CommRing T'] [Algebra c.F T']

abbrev Mx (Dw : Datum H) (T : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T

variable {y : FrPt Xo c R} {a : R →ₐ[c.F] T} {M M' N : Mx Dw T} {t t' r : T} {z z' : FrPt Xo c T} {w : FrPt Xo c T'}

include hS' hT

end Formalism.L2.Pj.FrCov
end
end

section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have key : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ((ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le).trans
    (add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl))

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg a)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C p.1 := hC p.1 p.2.1 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| :=
        Finset.single_le_sum (f := fun c => |C c|) (fun c _ => abs_nonneg _) (Finset.mem_univ _)
  | zero =>
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 0)) (iSup_le fun p => ?_)
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    simp
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) := by
  unfold goodOf
  split_ifs with hσ
  · exact hσ
  · have hx : ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ) ^ 2 + ((H.d : ℕ) : c.F) = 0 := by
      apply Subtype.ext
      have e : (((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
      push_cast [e]
      rw [H.sqrt_neg_disc_sq]
      ring
    have hy : (σ ((IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ)) ^ 2 = H.rt0 ^ 2 := by
      have h0 := congrArg σ hx
      rw [map_add (f := _), map_pow, map_natCast, map_zero] at h0
      rw [H.sqrt_neg_disc_sq]
      linear_combination h0
    have hre : H.rt0.re = 0 := by
      have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
      have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
      simp [sq] at h1 h2
      have hd : (0 : ℝ) < H.d := Nat.cast_pos.mpr H.d_prime.pos
      have e2 : H.rt0.re * H.rt0.im = 0 := by linear_combination h2 / 2
      have e3 : H.rt0.re ^ 4 = -(H.d * H.rt0.re ^ 2) := by
        linear_combination (H.rt0.re ^ 2) * h1 + (H.rt0.re * H.rt0.im) * e2
      have h4 : H.rt0.re ^ 4 ≤ 0 := by
        rw [e3]
        exact neg_nonpos.mpr (mul_nonneg hd.le (sq_nonneg _))
      have h5 : H.rt0.re ^ 4 = 0 := le_antisymm h4 (by positivity)
      exact (pow_eq_zero_iff (by norm_num)).mp h5
    have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
      apply Complex.ext <;> simp [hre]
    unfold GoodEmb at hσ ⊢
    simp only [RingHom.comp_apply] at hσ ⊢
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
    · exact absurd h hσ
    · rw [h, map_neg, hconj, neg_neg]

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := by
  unfold lieFac
  exact Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  unfold cusp at hf
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 σ) hσ
  exact supE_ne_top _ _ (Submodule.mem_comap.mp h2)

variable (U)

variable {U} {σ : c.F →+* ℂ}

end Formalism.L2.PjFree
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def exZ (Dw : Datum H) (G : WTZ E) : Ix Dw → ℤ
  | none => G.2
  | some x => G.1 (x.1, x.2)

theorem exZ_add (G G' : WTZ E) (i : Ix Dw) : exZ Dw (G + G') i = exZ Dw G i + exZ Dw G' i := by
  cases i <;> rfl

def frW (δ : Ix Dw → ℤ) (G : WTZ E) : ℤ := ∑ i, exZ Dw G i * δ i

theorem frW_add (δ : Ix Dw → ℤ) (G G' : WTZ E) : frW δ (G + G') = frW δ G + frW δ G' := by
  simp only [frW, exZ_add, add_mul, Finset.sum_add_distrib]

variable {Z : Comp Xo c}

def ordC (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) (x : AC Z) : ℤ :=
  WithTop.untopD 0 (v (x.coeff G)) + frW δ G

theorem ordC_single (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) (G : WTZ E) {r : Om Z} (hr : r ≠ 0) :
    ((ordC δ v G (AddMonoidAlgebra.single G r) : ℤ) : WithTop ℤ) = v r + (frW δ G : WithTop ℤ) := by
  have hv : v r ≠ ⊤ := fun h => hr ((AddValuation.top_iff v).1 h)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hv
  simp only [ordC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, ← hn, WithTop.untopD_coe]
  push_cast; rfl

theorem ordC_mul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G G' : WTZ E} {f g : AC Z}
    (hf : f ∈ AG Z G) (hg : g ∈ AG Z G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ordC δ v (G + G') (f * g) = ordC δ v G f + ordC δ v G' g := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  have hs : s ≠ 0 := fun h => hg0 (by simp [h])
  rw [AddMonoidAlgebra.single_mul_single]
  apply WithTop.coe_injective
  rw [ordC_single δ v _ (mul_ne_zero hr hs)]
  push_cast
  rw [ordC_single δ v _ hr, ordC_single δ v _ hs, AddValuation.map_mul, frW_add]
  push_cast
  ac_rfl

theorem ordC_smul (δ : Ix Dw → ℤ) (v : AddValuation (Om Z) (WithTop ℤ)) {G : WTZ E} {f : AC Z} (a : Om Z)
    (hf : f ∈ AG Z G) (hf0 : f ≠ 0) (ha : a ≠ 0) :
    ((ordC δ v G (a • f) : ℤ) : WithTop ℤ) = v a + (ordC δ v G f : WithTop ℤ) := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [AddMonoidAlgebra.smul_single', ordC_single δ v _ (mul_ne_zero ha hr), ordC_single δ v _ hr,
    AddValuation.map_mul, add_assoc]

abbrev sgOf (P : Om Z →+* ℂ) : c.F →+* ℂ := P.comp (algebraMap c.F (Om Z))

def PAlg (P : Om Z →+* ℂ) : Om Z →ₐ[c.F] CAt (sgOf P) :=
  { P with commutes' := fun _ => rfl }

def CBase (h : GenFrEx Xo c) (Z : Comp Xo c) (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ P, FrMap (PAlg P) (genFr h Z) (yP P)

def nrmC (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ) : ℝ :=
  ‖P (x.coeff G)‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)


variable (Xo c) in
def FnNe (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop := ∀ σ y i, fn σ y i ≠ 0

section nrm

variable (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
  (yP : ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))

theorem nrmC_zero (G : WTZ E) (P : Om Z →+* ℂ) : nrmC fn yP G 0 P = 0 := by
  simp only [nrmC, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero, norm_zero, zero_mul]

theorem nrmC_single (G : WTZ E) (r : Om Z) (P : Om Z →+* ℂ) :
    nrmC fn yP G (AddMonoidAlgebra.single G r) P = ‖P r‖ * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i) := by
  simp only [nrmC, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem nrmC_pos (hfn : FnNe Xo c fn) {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G) (hf0 : f ≠ 0) :
    0 < nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  have hr : r ≠ 0 := fun h => hf0 (by simp [h])
  rw [nrmC_single]
  refine mul_pos (norm_pos_iff.2 ((map_ne_zero P).2 hr)) (Finset.prod_pos fun i _ => ?_)
  exact zpow_pos (abs_pos.2 (hfn _ _ i)) _

theorem nrmC_mul (hfn : FnNe Xo c fn) {G G' : WTZ E} {f g : AC Z} (P : Om Z →+* ℂ) (hf : f ∈ AG Z G)
    (hg : g ∈ AG Z G') : nrmC fn yP (G + G') (f * g) P = nrmC fn yP G f P * nrmC fn yP G' g P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  obtain ⟨s, rfl⟩ := mem_AG.1 hg
  rw [AddMonoidAlgebra.single_mul_single, nrmC_single, nrmC_single, nrmC_single, map_mul, norm_mul]
  have : ∏ i, |fn _ (yP P) i| ^ (-exZ Dw (G + G') i) =
      (∏ i, |fn _ (yP P) i| ^ (-exZ Dw G i)) * ∏ i, |fn _ (yP P) i| ^ (-exZ Dw G' i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [exZ_add, neg_add, zpow_add₀ (abs_ne_zero.2 (hfn _ _ i))]
  rw [this]; ring

theorem nrmC_smul {G : WTZ E} {f : AC Z} (P : Om Z →+* ℂ) (a : Om Z) (hf : f ∈ AG Z G) :
    nrmC fn yP G (a • f) P = ‖P a‖ * nrmC fn yP G f P := by
  obtain ⟨r, rfl⟩ := mem_AG.1 hf
  rw [AddMonoidAlgebra.smul_single', nrmC_single, nrmC_single, map_mul, norm_mul, mul_assoc]

end nrm


variable (Xo c) in
def FnConj (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ Z (G : WTZ E) (x : AC Z) (P : Om Z →+* ℂ),
    nrmC fn (yP Z) G x ((starRingEnd ℂ).comp P) = nrmC fn (yP Z) G x P

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def BorDesc : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
    ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R) (yq : FrPt Xo c q.R),
      FrMap φ yp y → FrMap ψ yq y' →
      ∃ (r : TRing c.F) (α : p.R →ₐ[c.F] r.R) (β : q.R →ₐ[c.F] r.R) (χ : r.R →ₐ[c.F] S)
        (z z' : FrPt Xo c r.R) (t₀ : Ix Dw → (r.R)ˣ),
        χ.comp α = φ ∧ χ.comp β = ψ ∧ FrMap α yp z ∧ FrMap β yq z' ∧ FrBor t₀ z z' ∧
          ∀ i, χ (t₀ i : r.R) = (t i : S)

def IntLatU : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io), letI := io.toAlgebra; y'.1.x = y.1.x →
    (∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧
      ∀ i, IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.1.u τ i)) ∧
    ∀ (a : T.Frˣ) (pm : Gx y'.1.x ⟶ Gx y.1.x),
      pm ≫ (CartesianMonoidalCategory.snd (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.snd (Over.mk y'.1.x) Xo.univ.t.G).left →
      pm ≫ (CartesianMonoidalCategory.fst (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.fst (Over.mk y'.1.x) Xo.univ.t.G).left →
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.1.x).U i ≤ pm ⁻¹ᵁ (PPx y.1.x).U i),
        (pm.appLE _ _ h).hom (scal y.1.x (a : T.Fr) i * y.1.s.f i) = y'.1.s.f i) →
      valV T.V (a : T.Fr) = 1

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem wtField_of (hD : BorDesc Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    obtain ⟨r, α, β, χ, z, z', t₀, hα, hβ, hz, hz', hb₀, ht⟩ := hD S t y y' hb p q φ ψ yp yq hp hq
    rw [← hα, ← hβ, AlgHom.comp_apply, AlgHom.comp_apply, ← hf.1 p r α yp z hz, ← hf.1 q r β yq z' hz',
      hf.2 r t₀ z z' hb₀, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec

theorem valV_algebraMap_unit (T : CDVR) {u : T.V} (hu : IsUnit u) :
    valV T.V (algebraMap T.V T.Fr u) = 1 := by
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro h
  exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem intDiagUnit_of (hL : IntLatU Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t hb k
  let := io.toAlgebra
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hb
  obtain ⟨hA, hG⟩ := (show IntLatU Xo c from hL) T io y y' hx
  rcases k with _ | ⟨τ, i⟩
  · exact hG (t none) pm h1 h2 h3
  obtain ⟨A, hdet, hAc⟩ := hA τ

  have hrow : ∀ i', ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i' = (t (some ⟨τ, i'⟩) : T.Fr) ∧
      (∀ j, i' < j → cf j = 0) ∧ ∀ j, algebraMap T.V T.Fr (A i' j) = cf j := by
    intro i'
    obtain ⟨cf, hci, hcz, hcomb⟩ := hu τ i'
    have htan : IsTanAt y.1.x (y'.1.u τ i') := hx ▸ y'.1.tan τ i'
    obtain ⟨a0, -, huniq⟩ := y.1.basis τ (y'.1.u τ i') htan (y'.1.eig τ i')
    have e1 := huniq cf hcomb
    have e2 := huniq _ (hAc i')
    exact ⟨cf, hci, hcz, fun j => congrFun (e2.trans e1.symm) j⟩
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hlow : A.IsLowerTriangular := by
    intro i' j hij
    obtain ⟨cf, -, hcz, hA'⟩ := hrow i'
    apply hinj
    rw [hA' j, hcz j hij, map_zero]
  rw [Matrix.det_of_isLowerTriangular A hlow, IsUnit.prod_univ_iff] at hdet
  obtain ⟨cf, hci, -, hA'⟩ := hrow i
  rw [← hci, ← hA' i]
  exact valV_algebraMap_unit T (hdet i)

end Proofs

end Formalism.L2.Pj
end
end

section

noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

variable (Xo c)

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

end Formalism.L2.PjFree
end
end
