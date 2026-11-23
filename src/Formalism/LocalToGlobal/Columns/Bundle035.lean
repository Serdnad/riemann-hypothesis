module

public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.KernelLattices.Bundle002
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Sum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhs_cosets_finite (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) : (mhlCosets hc (n := n) v U k).Finite := by
  have hB := mhl_split_bij' hc U k ST SG hov hST hSG hsp hk 1
  refine Set.Finite.of_finite_image ?_ hB.injOn
  rw [hB.image_eq]
  exact DecoSet.heckeSet_finite (conjPrime₂ Pb).ne_bot (conjIdeal_ne_bot (conjPrime₂ Pb).ne_bot) k _

theorem mhs_exists_reps (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) :
    ∃ R : Finset (UAd hc n), Set.BijOn (fun η : UAd hc n => (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v)) R
      (mhlCosets hc v U k) := by
  classical
  have hfin := mhs_cosets_finite hc U k ST SG hov hST hSG hsp hk
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro η hη
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη
    obtain ⟨c, hc', rfl⟩ := hη
    show (QuotientGroup.mk c.out : UAd hc n ⧸ mhlKv hc n v) ∈ mhlCosets hc v U k
    rw [QuotientGroup.out_eq']
    exact hc'
  · intro η hη η' hη' h
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη hη'
    obtain ⟨c, -, rfl⟩ := hη
    obtain ⟨c', -, rfl⟩ := hη'
    have h' : c = c' := (QuotientGroup.out_eq' c).symm.trans (h.trans (QuotientGroup.out_eq' c'))
    rw [h']
  · intro c hc'
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
    exact ⟨c, hc', rfl⟩

theorem mhs_decoOf_out (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (x η : UAd hc n) :
    decoOf ST SG ((x * (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoOf ST SG ((x * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) η
  rw [e, ← mul_assoc, Subgroup.coe_mul]
  exact decoOf_mul_mhlKv ST SG hST hSG _ h.2

end Sum

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix MvPolynomial
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

structure LevCh (X : Fields) (Pr : Primes X) (R : Ranks) where
  β : ℕ → Type
  [finβ : ∀ j, Fintype (β j)]
  [decβ : ∀ j, DecidableEq (β j)]
  lev : ∀ j, β j → LevFam X.E X.K (R.N j) Pr.vGs

attribute [instance] LevCh.finβ LevCh.decβ

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)



end Step

section RhoPt

variable {X : Fields} {Pr : Primes X} {R : Ranks}


open Classical in
def rhoPt (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs)) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N i) := ⟨(R.N_pos i).ne'⟩
    (Formalism.L2.DIV.detTw hc.sig (Dc.muAt i) (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi (ptOf hc (R.N i) (Pr.vT u) Pr.vGs p : GL (Fin (R.N i)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^
        (-((R.N (i + 1) / 2 : ℕ) : ℤ))
  else 1


open Classical in
def rhoPt' (Dc : DetChr X R.m) {u : Pr.Word} (i : ℕ) (p : DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs)) : X.Kˣ :=
  if hc : Formalism.BasicNotions.CMData X.F X.E then
    letI : NeZero (R.N (i + 1)) := ⟨(R.N_pos (i + 1)).ne'⟩
    Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
              (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) *
      (Formalism.L2.DIV.detTw hc.sig Dc.chi
        (ptOf hc (R.N (i + 1)) (Pr.vT u) Pr.vGs p : GL (Fin (R.N (i + 1))) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) ^ (((R.N i / 2 : ℕ) : ℤ))
  else 1

end RhoPt

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R)

variable {W Λ}

end Chain

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFamC (Λ : LevCh X Pr R) (u : Pr.Word) : Type :=
  ∀ i, Λ.β i → Λ.β (i + 1) → DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs) → DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs) →
    HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFamC Λ u)


variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Unf

variable {X : Fields}

def frCo (σ₀ : X.K →+* ℂ) (n : ℕ) : FrS X σ₀ n → X.Tau → Matrix (Fin n) (Fin n) ℂ := fun y τ => y.1 τ

def polFn (σ₀ : X.K →+* ℂ) (n : ℕ) : Pol ℂ X.Tau n →ₗ[ℂ] (FrS X σ₀ n → ℂ) := frPolyG (frCo σ₀ n)

theorem polFn_apply (σ₀ : X.K →+* ℂ) (n : ℕ) (Q : Pol ℂ X.Tau n) (y : FrS X σ₀ n) :
    polFn σ₀ n Q y = eval (fun x : X.Tau × Fin n × Fin n => y.1 x.1 x.2.1 x.2.2) Q := rfl

theorem polFn_injective (σ₀ : X.K →+* ℂ) (n : ℕ) : Function.Injective (polFn (X := X) σ₀ n) :=
  frPolyG_inj (frCo σ₀ n) fun f hf => ⟨⟨f, fun τ => (hf τ).isUnit⟩, rfl⟩

end Unf

section BaseChange

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

theorem map_jetLin (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem map_subD (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]
      split_ifs with hv
      · simp
      · simp
  exact RingHom.congr_fun h P

theorem map_frDet (σ : K →+* L) (τ : ι) : MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

theorem map_jetMap (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (MvPolynomial.map σ P) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

theorem jetMap_shift (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J (fun _ => 0) (P * ∏ τ, frDet K a τ ^ n τ) = jetMap J n P := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one]

theorem eval_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) (frDet ℂ a τ) = (y τ).det := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

end BaseChange

section Ev

variable {X : Fields} {a b : ℕ}

end Ev

section Arg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

variable {W Λ}

end Arg

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Wt

section Zero

variable {X : Fields}

end Zero

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))


open Classical in
def frsD {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := Pr.vGs)) : Frs X.E n (rowSG Pr sel mu) := fun P =>
  if h : P.1 ∈ Pr.vGs then p.1.liftFr ⟨P.1, h⟩ else 1

def repN (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Submodule (𝓞 X.E) (Sp X.E (R.N j)) := ((stepGSD W Λ u j).outSec.rep c).1.N

def repFr (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Frs X.E (R.N j) (rowSG Pr sel mu) := frsD sel mu ((stepGSD W Λ u j).outSec.rep c)

def RhoScal {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Am : Amb X) (u : Pr.Word) : Prop :=
  ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    σ₀ (rhoK W Λ G.chr u i c : X.K) * σ₀ (rhoK' W Λ G.chr u i c' : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') =
      σ₀ (scalK Ch sel mu cst i (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c'))

variable {W Λ Ch sel mu cst}

end Rho

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFam (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Type :=
  ∀ i, DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs) → DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs) → HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFam Pr R u)

def xiKer (i : ℕ) (p : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs)) (p' : DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs)) :
    (stepGSD W Λ u i).V →ₗ[X.K] (stepGSD W Λ u (i + 1)).V :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    p.1.N (frsD sel mu p) p'.1.N (frsD sel mu p') (Ξ i p p')

def XiEquiv : Prop :=
  ∀ i, ClsEq (S := stepGSD W Λ u i) (S' := stepGSD W Λ u (i + 1)) (xiKer W Λ Ch sel mu cst Am u Ξ i)


variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Charts

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))


open Classical in
def cplAt (u : Pr.Word) (m2 j : ℕ) (b : L.β j) : Cpl ((chF W sel mu L u j).mem b) where
  Yb := Set (Sp X.E (R.N j))
  actY :=
    { smul := fun g Y => (fun v => g.1.1 v) '' Y
      one_smul := fun Y => Set.image_id Y
      mul_smul := fun g h Y => (Set.image_image (fun v => g.1.1 v) (fun v => h.1.1 v) Y).symm }
  ys p := if j = m2 + 1 then ybSet sel mu cst p.deco.1.N else {Set.univ}
  fin p := by
    split_ifs
    · exact ybSet_finite sel mu cst _ p.deco.2.lat.fg
    · exact Set.finite_singleton _
  equiv g p Y := by
    split_ifs
    · exact ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y
    · show (fun v => g.1.1 v) '' Y = Set.univ ↔ Y = Set.univ
      constructor
      · intro h
        have h2 : (fun v => g.1.1 v) '' Y = (fun v => g.1.1 v) '' Set.univ := by
          rw [h, Set.image_univ]
          exact (g.1.1.surjective.range_eq).symm
        exact g.1.1.injective.image_injective h2
      · rintro rfl
        rw [Set.image_univ]
        exact g.1.1.surjective.range_eq

@[reducible] def chFY (u : Pr.Word) (m2 j : ℕ) : GFam X.K where
  β := L.β j
  V := (colValF W sel mu u j).V
  ιV := VVIdx (colValF W sel mu u j).lam
  bV := (colValF W sel mu u j).bV
  pair := (colValF W sel mu u j).pair
  G b := FrmG (L.levG j b) (L.levQ j b)
  D b := (cplAt W sel mu cst L u m2 j b).Pts
  actD b := (cplGSD (cplAt W sel mu cst L u m2 j b)).actD
  ρ b := frmRho (colValF W sel mu u j) (L.levG j b) (L.levQ j b)
  Nab _ p := (colValF W sel mu u j).Nab p.1.1
  Del _ p := (colValF W sel mu u j).Del p.1.1

variable {W sel mu cst L}

variable {Ch}

end Charts

end Formalism.L2.Col
end
end
