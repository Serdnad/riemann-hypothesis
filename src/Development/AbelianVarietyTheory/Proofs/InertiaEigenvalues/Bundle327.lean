module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle299
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle291
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle301
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.coboundary_semistableTensor_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMonCob.coboundary_cols | exact GlobalTheory.PMonCob.coboundary_cols | (intros; apply GlobalTheory.PMonCob.coboundary_cols <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.coboundary_tmul_of_column_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  first | exact @GlobalTheory.CobColumn.coboundary_tmul_of_column | exact GlobalTheory.CobColumn.coboundary_tmul_of_column | (intros; apply GlobalTheory.CobColumn.coboundary_tmul_of_column <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.Pass.LocDirect

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRing : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

def ModuleGaloisRepresentation {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

abbrev fam (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) :=
  Br.loc D.nbr i w hw (rTwO D.nd i r x)

def toLLv {a n : ℕ} (y : Fin a → Fin n → KK D.nd i) : Fin a → Fin n → Br.LL D.nbr i w hw :=
  fun j m => Br.toLLK (D.nbr i w hw) (y j m)

theorem loc_mulVec {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (v : Fin k → KK D.nd i) :
    (Br.loc D.nbr i w hw M g).mulVec (fun m => Br.toLLK (D.nbr i w hw) (v m)) =
      fun m => Br.toLLK (D.nbr i w hw)
        ((mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).mulVec v m) := by
  funext m
  rw [RingHom.map_mulVec]
  congr 1
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

def XV {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) :=
  Submodule.span _ (toLLv i w hw '' (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)))

theorem XV_stable {a : ℕ} (x : Fin a → D.nd.X i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (g : Br.G D.nbr i w hw) :
    ∀ u ∈ XV i w hw Y, sumRho (fun j : Fin a => fam i w hw r (x j)) id g u ∈ XV i w hw Y := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨_, hst ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) y hy, ?_⟩
    funext j
    rw [sumRho_apply]
    exact (loc_mulVec i w hw _ g (y j)).symm
  | zero => simp
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [map_smul]; exact Submodule.smul_mem _ c hu

def Xgrep {a : ℕ} (x : Fin a → D.nd.X i)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GRep.sub (GRep.sum (Qp := ℚ_[D.nd.l i]) (O := Br.OLL D.nbr i w hw) (fun j : Fin a => fam i w hw r (x j))
    (fun j v => (hc j).matrix_mulVec continuous_const) id) (XV i w hw Y) (XV_stable i w hw r x Y hst)

def pushSet {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) {a : ℕ} (x : Fin a → D.nd.X i)
    (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (hE : ∀ γ : GE D.nd,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y) :
    Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :=
  {c | ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
      (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
      c = fun g => Br.phi (D.nbr i w hw) k
        (φ ⟨_, hE ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)⟩)}

theorem mem_cutCoc (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (c : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) :
    c ∈ cutCoc i w hw r Xs M ↔ ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG)
      (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
      (hE : ∀ γ : GE D.nd,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y),
      c ∈ pushSet i w hw r M x E Y hst hE := Iff.rfl
end GlobalTheory.Pass.LocDirect
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR


open Fin.NatCast in
theorem eq_zero_of_sum_kd_mul_U0_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x : Fin r × n), (∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * (U x.1 : Matrix n n P.R.BdR) i x.2 ∈ Fil P 1 → c = 0) → ∀ c : n × Fin r → ↥(MaximalUnramifiedExtension l), (∀ i, fr l 1 (c i) = c i) → ∑ i, kd P (c i) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i (x.2, x.1) ∈ Fil P 1 → c = 0 := by
  intro l _ P r ω hω hdet n _ _ U x hx c hc hsum
  haveI : NeZero r := ⟨fun h => by subst h; exact x.1.elim0⟩
  set Q : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((resGL n ω hdet)⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)).val with hQ
  have hQp : Q * resMat n ω = 1 := (resGL n ω hdet).inv_mul
  set d := Matrix.vecMul c Q with hd_def
  have hcd : c = Matrix.vecMul d (resMat n ω) := by
    rw [hd_def, Matrix.vecMul_vecMul, hQp, Matrix.vecMul_one]
  have hexp : ∀ i k, c (i, k) = ∑ m : Fin r, d (i, m) * fr l m (ω k) := by
    intro i k
    conv_lhs => rw [hcd]
    simp only [Matrix.vecMul, dotProduct, resMat_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hrel : ∀ i (m : Fin r), d (i, m + 1) = fr l 1 (d (i, m)) := by
    intro i
    have hv : Matrix.vecMul (fun m' : Fin r => fr l 1 (d (i, m' - 1)) - d (i, m')) (frobMat ω) = 0 := by
      funext k
      simp only [Matrix.vecMul, dotProduct, frobMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply]
      rw [← hexp i k]
      have h1 : ∑ m' : Fin r, fr l 1 (d (i, m' - 1)) * fr l m' (ω k)
          = ∑ m : Fin r, fr l 1 (d (i, m)) * fr l 1 (fr l m (ω k)) := by
        refine (Fintype.sum_equiv (Equiv.addRight (1 : Fin r)) _ _ fun m => ?_).symm
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
        congr 1
        rw [← fr_add, ← fr_mod (hω k) ((m + 1 : Fin r) : ℕ), ← fr_mod (hω k) (1 + (m : ℕ))]
        congr 1
        rw [Fin.val_add, Nat.mod_mod, add_comm]
        rcases Nat.lt_or_ge 1 r with h | h
        · rw [Fin.val_one', Nat.mod_eq_of_lt h]
        · have : r = 1 := by have := NeZero.ne r; omega
          subst this; simp
      rw [h1]
      simp_rw [← map_mul]

      rw [← map_sum, ← hexp i k, hc (i, k), sub_self]
    have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    intro m
    have := congrFun h0 (m + 1)
    simp only [add_sub_cancel_right, Pi.zero_apply, sub_eq_zero] at this
    exact this.symm
  have hprop : ∀ i (k : ℕ), d (i, x.1 + (k : Fin r)) = fr l k (d (i, x.1)) := by
    intro i k
    induction k with
    | zero => simp [fr_zero]
    | succ k ih => rw [Nat.cast_succ, ← add_assoc, hrel, ih, ← fr_add, add_comm]
  have hfix : ∀ i, fr l r (d (i, x.1)) = d (i, x.1) := by
    intro i; rw [← hprop, Fin.natCast_self, add_zero]
  have hU0 : (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR)
      = Q.map (kd P) * Matrix.blockDiagonal (fun m => (U m : Matrix n n P.R.BdR)) := rfl
  have hid : ∑ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
      = ∑ j, kd P (d (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
    have step : ∀ a, kd P (c a) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) a (x.2, x.1)
        = ∑ j, kd P (c a) * kd P (Q a (j, x.1)) * (U x.1 : Matrix n n P.R.BdR) j x.2 := by
      intro a
      rw [hU0]
      simp only [Matrix.mul_apply, Matrix.blockDiagonal_apply, Matrix.map_apply, Fintype.sum_prod_type, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_

    simp only [hd_def, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul]
  have hzero : (fun j => d (j, x.1)) = 0 := hx _ hfix (hid ▸ hsum)
  have hd0 : d = 0 := by
    funext ⟨i, m⟩
    have hm : m = x.1 + (((m - x.1 : Fin r) : ℕ) : Fin r) := by simp
    rw [hm, hprop, show d (i, x.1) = 0 from congrFun hzero i, map_zero]
    rfl
  rw [hcd, hd0, Matrix.zero_vecMul]

end GlobalTheory.PMon.ResR
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem colv_latC_and_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  intro l _ P r ω hω hdet n _ _ U x y A₀ hA W₀ hW hev
  have hit : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] b = (P.φB ^ m) b := fun m b => by rw [AlgHom.coe_pow]
  have hfix : ∀ (m : ℕ) i j, P.φB^[m] ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun m i j => Function.iterate_fixed (hA i j) m
  have hφcol : ∀ (m : ℕ) c i, P.φB^[m] (colv P ω A₀ c i) =
      ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c := by
    intro m c i

    rw [hit, colv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hit, ← hit, phi_iter_kur, hfix]
  have hsum : ∀ {R : Type} [CommRing R] (f : ↥(MaximalUnramifiedExtension l) →+* R) (X : Matrix (n × Fin r) (n × Fin r) R) (m : Fin r) (i : n) c,
      ∑ k, f (fr l m (ω k)) * X (i, k) c = ((resMat n ω).map f * X) (i, m) c := by
    intro R _ f X m i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [resMat_apply, apply_ite f, ite_mul]
  have hpU : (resMat n ω).map (kd P) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
      Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR) := by
    have e : (resMat n ω).map (kd P) = ((Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
        Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) : GL (n × Fin r) P.R.BdR) :
        Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
    rw [e, U0, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rfl
  have h0 : ∀ e f, P.ιB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) e f) =
      ((U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) e f := by
    intro e f; rw [← hev]; rfl
  have hcol : ∀ (m : Fin r) c i, ev P m (colv P ω A₀ c i) =
      ∑ j, (U m : Matrix n n P.R.BdR) i j * tz P (eps x y (m, j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c := by
    intro m c i

    rw [ev, hφcol, map_sum]
    simp only [map_mul, iota_kur, h0]
    rw [hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_mul, ite_mul, mul_assoc]
  refine ⟨fun c => ⟨fun i => ?_, fun m => ⟨fun j => (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c,
    fun j => hW.1 _ _, funext fun i => ?_⟩⟩, ?_⟩
  · rw [hφcol]; simp only [hω]; rfl
  · rw [hcol]; simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
  · haveI : Nontrivial P.R.BdR := ⟨⟨(P.PD (botExt l)).ι (P.PD (botExt l)).t, 0, fun h =>
      (P.PD (botExt l)).not_mem_filtration_two (by rw [h]; exact zero_mem _)⟩⟩
    haveI : Nontrivial P.R.B := ⟨⟨1, 0, fun h => one_ne_zero (by simpa using congrArg P.ιB h : (1 : P.R.BdR) = 0)⟩⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ c, g c • colv P ω A₀ c i = 0 := fun i => by
      have := congrFun hg i; simpa [Finset.sum_apply] using this
    have hYe : ∀ i (m : Fin r) c, Ymat P ω A₀ (i, m) c = P.φB^[m] (colv P ω A₀ c i) := by
      intro i m c
      rw [hφcol, hsum, Ymat]
    have hY : (Ymat P ω A₀).mulVec (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      funext ⟨i, m⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      calc ∑ c, Ymat P ω A₀ (i, m) c * algebraMap ℚ_[l] P.R.B (g c)
          = (P.φB ^ (m : ℕ)) (∑ c, g c • colv P ω A₀ c i) := by

            rw [map_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [hYe, hit, map_smul, Algebra.smul_def, mul_comm]
        _ = 0 := by rw [hg' i, map_zero]
    have hdetY : IsUnit (Ymat P ω A₀).det := by
      rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((isUnit_det_resMat n ω hdet).map _).mul ((Matrix.isUnit_iff_isUnit_det _).1 A₀.isUnit)
    have hv0 : (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      have := congrArg (Matrix.mulVec (Ymat P ω A₀)⁻¹) hY
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetY, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    intro c
    exact (algebraMap ℚ_[l] P.R.B).injective (by simpa using congrFun hv0 c)

end GlobalTheory.PMon.ResR
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem fil_mul_entries {n : Type} [Fintype n] {A B : Matrix n n P.R.BdR}
    (hA : ∀ i j, A i j ∈ Fil P 0) (hB : ∀ i j, B i j ∈ Fil P 0) : ∀ i j, (A * B) i j ∈ Fil P 0 :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Fil_sum fun k _ => Fil_mul_left (hA i k) (hB k j)

theorem fil_blockDiagonal_entries {r : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (V : Fin r → Matrix n n P.R.BdR) (h : ∀ m i j, V m i j ∈ Fil P 0) :
    ∀ a b, Matrix.blockDiagonal V a b ∈ Fil P 0 := fun a b => by
  rw [Matrix.blockDiagonal_apply]
  split_ifs
  · exact h _ _ _
  · exact Fil_zero_mem 0

theorem fil_kd_entries {m : Type} [Fintype m] [DecidableEq m] (g : GL m ↥(MaximalUnramifiedExtension l)) :
    ∀ a b, ((Units.map ((kd P).mapMatrix : Matrix m m ↥(MaximalUnramifiedExtension l) →+* Matrix m m P.R.BdR).toMonoidHom g :
      GL m P.R.BdR) : Matrix m m P.R.BdR) a b ∈ Fil P 0 := fun a b => by
  rw [Units.coe_map]
  exact kd_mem_Fil P _

theorem unitM_U0_of_unitM : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR),
    (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  intro l _ P r ω hdet n _ _ U hU
  constructor
  · unfold U0
    rw [Units.val_mul, ← map_inv]
    exact fil_mul_entries (fil_kd_entries _)
      (fil_blockDiagonal_entries _ fun m i j => (hU m).1 i j)
  · unfold U0
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    exact fil_mul_entries
      (fil_blockDiagonal_entries _ fun m i j => (hU m).2 i j) (fil_kd_entries _)

end GlobalTheory.PMon.ResR
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc
theorem twistM_repV_cont : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ), (Continuous fun g => M g) → Continuous (fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1)) → ∀ x, Continuous fun g => repV C (twistM (locOC C M) θ) g x := by
  intro D i w hw C k M θ hM hθ x
  have hinc : Continuous fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1) := by
    have e : (fun y : ↥(OL (D.nbr i w hw).LL) => ((incO C.le y : ↥(OL C.LL)) : ↥C.LL.1)) =
        fun y => IntermediateField.inclusion C.le y.1 := rfl
    rw [e]
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hmat : Continuous fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g := by
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous fun g : Br.G D.nbr i w hw =>
        M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b :=
      (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.ι_cont (D.nbr i w hw)))
    have h2 := hinc.comp ((D.nbr i w hw).eO_cont.comp h1)
    have e : (fun g => mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g a b) =
        fun g => ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) θ g : (↥C.LL.1)ˣ) : ↥C.LL.1) *
          ((incO C.le ((D.nbr i w hw).eO (M ((decS D.nd w) ((Br.ι (D.nbr i w hw)) g)) a b)) : ↥(OL C.LL)) : ↥C.LL.1) := by
      funext g
      simp [mapM, twistM, locOC, Br.locO, tableLineDegreeTwo.charL, Matrix.smul_apply]
    rw [e]
    exact hθ.mul h2
  have e2 : (fun g => repV C (twistM (locOC C M) θ) g x) =
      fun g => (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (twistM (locOC C M) θ) g).mulVec x := by
    funext g
    rfl
  rw [e2]
  exact hmat.matrix_mulVec continuous_const
end GlobalTheory.UseLoc
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem chiRat_eq_epsU_zpow (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) : chiU D.nd i c * (chiU D.nd i 1)⁻¹ = epsU D.nd i ^ (-((c : ℤ) - 1)) := by
    show D.nd.chi i c * (D.nd.chi i 1)⁻¹ = _
    rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
    rfl

theorem charL_chiOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C χ) g =
      Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw χ g) := by
    apply Units.ext
    rfl

theorem inc_cycLL_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g) : Units.map C.inc.toMonoidHom (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g := by
    apply Units.ext
    exact (IntermediateField.inclusion C.le).commutes _

theorem locChi_zpow_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (k : ℤ) (g) : Br.locChi D.nbr i w hw (χ ^ k) g = Br.locChi D.nbr i w hw χ g ^ k := by
    show Units.map _ ((χ ^ k) _) = (Units.map _ (χ _)) ^ k
    rw [MonoidHom.zpow_apply, map_zpow]

theorem charL_mul_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (a b : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (a * b) g =
      tableLineDegreeTwo.charL (LL := ↥C.LL.1) a g * tableLineDegreeTwo.charL (LL := ↥C.LL.1) b g := by
    show Units.map _ ((a * b) g) = _
    rw [MonoidHom.mul_apply, map_mul]
    rfl

theorem locChi_one_apply (g : Br.G D.nbr i w hw) : Br.locChi D.nbr i w hw (1 : GE D.nd →* (D.nd.O i)ˣ) g = 1 := by
    simp [Br.locChi, Br.chiG]

theorem inc_locChi_epsU_zpow (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) (k : ℤ) :
    Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw (epsU D.nd i) g ^ k) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ k := by
  rw [map_zpow, ← inc_cycLL_apply C g, GlobalTheory.CycBridge.locChi_epsU D i w hw g]

theorem chiT_cyc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → ∀ g, tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g = tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
  intro D i w hw C θ c h1 h2 g
  have e1 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) g =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
    rw [charL_chiOC_apply, chiRat_eq_epsU_zpow c h1 h2, locChi_zpow_apply, inc_locChi_epsU_zpow]
  have e0 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) g = 1 := by
    rw [charL_chiOC_apply, mul_inv_cancel, locChi_one_apply]
    exact map_one _
  unfold chiT
  rw [charL_mul_apply, charL_mul_apply, e1, e0, one_mul]
  exact mul_comm _ _

end GlobalTheory.UseLoc
end
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), Lev l s → ∀ u ∈ FilB P 0, io AI AI.π₁ * u = 1 → ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l, (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | exact GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | (intros; apply GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat <;> assumption)
end
