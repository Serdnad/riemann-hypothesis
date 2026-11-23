module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle178
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace

namespace GlobalTheory.FlagEmb

section Lin

variable {T : Type} (m : T → ℕ)

abbrev Let : Type := Σ τ : T, Fin (m τ)

abbrev CellVar : Type := Σ τ : T, {ij : Fin (m τ) × Fin (m τ) // ij.2 < ij.1}

abbrev Pm : Type := ∀ τ : T, Equiv.Perm (Fin (m τ))

variable {m} {S : Type} [CommRing S] {M : ℕ}

def cell (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) : S :=
  if h : j < i then x ⟨τ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0

def cellVec {ι : Type} (c : Let m → ι → S) (w : Pm m) (x : CellVar m → S) : Let m → ι → S :=
  fun z => ∑ i, cell x z.1 i z.2 • c ⟨z.1, w z.1 i⟩

def wLet (w : Pm m) (z : Let m) : Let m := ⟨z.1, w z.1 z.2⟩

def Down {k : ℕ} (e : Fin k → Let m) : Prop :=
  Function.Injective e ∧ ∀ (l : Fin k) (j : Fin (m (e l).1)), j < (e l).2 → ∃ l', e l' = ⟨(e l).1, j⟩

def std (τ : T) (k : ℕ) (h : k ≤ m τ) : Fin k → Let m := fun l => ⟨τ, Fin.castLE h l⟩

theorem down_std (τ : T) (k : ℕ) (h : k ≤ m τ) : Down (std τ k h) := by
  refine ⟨fun a b hab => ?_, fun l j hj => ⟨⟨j, lt_trans hj l.2⟩, rfl⟩⟩
  have := congrArg (fun z : Let m => (z.2 : ℕ)) hab
  exact Fin.ext this


variable (m) in
abbrev En : Type := Σ k : ℕ, {e : Fin k → Let m // Down e}

abbrev stdEn (τ : T) (k : ℕ) (h : k ≤ m τ) : En m := ⟨k, std τ k h, down_std τ k h⟩

instance finite_en [Finite T] : Finite (En m) := by
  have := Fintype.ofFinite (Let m)
  refine Finite.of_surjective (fun a : Σ k : Fin (Fintype.card (Let m) + 1), {e : Fin k → Let m // Down e} =>
    (⟨a.1, a.2⟩ : En m)) ?_
  rintro ⟨k, e⟩
  have hk : k ≤ Fintype.card (Let m) := by simpa using Fintype.card_le_of_injective _ e.2.1
  exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩, rfl⟩

def plN (M k : ℕ) : ℕ := (M + 1) ^ k - 1

def plE (M k : ℕ) : Fin (plN M k + 1) ≃ (Fin k → Fin (M + 1)) :=
  (finCongr (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos M)))).trans finFunctionFinEquiv.symm

def plk {ι : Type} {k : ℕ} (c : ι → Fin (M + 1) → S) (e : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => (Matrix.of fun l l' => c (e l) (plE M k q l')).det

def lform {ι : Type} {k : ℕ} (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => ∏ l, D (ρ l) (plE M k q l)


open Classical in
def LeftInv {ι : Type} (D c : ι → Fin M → S) : Prop := ∀ z z', ∑ r, D z r * c z' r = if z = z' then 1 else 0

def Tri {ι : Type} (c c' : Let m → ι → S) (d : Let m → S) : Prop :=
  ∀ z : Let m, c' z - d z • c z ∈ Submodule.span S ((fun j : Fin (m z.1) => c ⟨z.1, j⟩) '' {j | j < z.2})

def InBlock {ι : Type} (c c' : Let m → ι → S) : Prop :=
  ∀ z : Let m, c' z ∈ Submodule.span S (Set.range fun j : Fin (m z.1) => c ⟨z.1, j⟩)

theorem map_plk {ι : Type} {k : ℕ} {S' : Type} [CommRing S'] (φ : S →+* S') (c : ι → Fin (M + 1) → S) (e : Fin k → ι) :
    φ ∘ plk c e = plk (fun z => φ ∘ c z) e := by
  funext q
  simp only [plk, Function.comp_apply, RingHom.map_det]
  rfl

theorem map_cellVec {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') (c : Let m → ι → S) (w : Pm m)
    (x : CellVar m → S) (z : Let m) : φ ∘ cellVec c w x z = cellVec (fun z => φ ∘ c z) w (φ ∘ x) z := by
  funext r

  simp only [cellVec, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold cell
  split_ifs <;> simp

theorem LeftInv.map {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') {D c : ι → Fin M → S} (h : LeftInv D c) :
    LeftInv (fun z => φ ∘ D z) (fun z => φ ∘ c z) := fun z z' => by
  have := congrArg φ (h z z')

  simp only [map_sum, map_mul] at this
  refine this.trans ?_
  split_ifs <;> simp

end Lin

section Geo

variable {O K : Type} [CommRing O] [Field K] (β : O →+* K) {X : Scheme.{0}} (s : X ⟶ Sp O) {T : Type} {m : T → ℕ}
  {M : ℕ} {B : Type} (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))

structure IsCover (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) : Prop where
  ovr : ∀ b, (V b).2.fromSpec ≫ s = spMap ((α b).comp β)
  inv : ∀ b, LeftInv (D b) (c b)
  compat : ∀ (k : Type) [Field k] b b' (φ : Γ(X, (V b).1) →+* k) (φ' : Γ(X, (V b').1) →+* k),
    spMap φ ≫ (V b).2.fromSpec = spMap φ' ≫ (V b').2.fromSpec →
      InBlock (fun z => φ ∘ c b z) (fun z => φ' ∘ c b' z)


variable (m) in
abbrev CR (U : X.affineOpens) : Type := MvPolynomial (CellVar m) Γ(X, U.1)


variable (m) in
def cbase (U : X.affineOpens) : Sp (CR m U) ⟶ X := spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U) ≫ U.2.fromSpec

def uvec {U : X.affineOpens} (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : Let m → Fin (M + 1) → CR m U :=
  cellVec (fun z => MvPolynomial.C ∘ c z) w MvPolynomial.X

variable (c : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1))

structure HasPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop where
  base : ∀ b w, h b w ≫ p0 = cbase m (V b)
  plk : ∀ b w en, ∃ hu, h b w ≫ p en =
    pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1) hu

structure IsPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop extends HasPlk β V α c p0 p h where
  proj : IsProjOver (p0 ≫ s)
  ovr : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s
  ext : ∀ (Z : Scheme.{0}) (a a' : Z ⟶ P), a ≫ p0 = a' ≫ p0 → (∀ en, a ≫ p en = a' ≫ p en) → a = a'

def IsCellOpen {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (W : P.Opens) : Prop :=
  ∀ (k : Type) [Field k] (z : Sp k ⟶ P), Set.range z ⊆ W ↔ ∃ φ : Γ(X, U.1) →+* k, z ≫ p0 = spMap φ ≫ U.2.fromSpec ∧
    ∀ τ j hj (b : O →+* k) v hv, z ≫ p (stdEn τ j hj) = pt b v hv →
      ∑ q, φ (lform D (wLet w ∘ std τ j hj) q) * v q ≠ 0

end Geo

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev Tn (R : Type) [CommRing R] : Type := Sp (DualNumber R) ⟶ t.G.left


open GlobalTheory.FactorDepth in
theorem exists_comb {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    (a : Fin n → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u a w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun j => smT_zero_ovT _) a),
    (isCombAtG_iff t x (fun j => ovT (hu j)) a _).2 rfl⟩


open GlobalTheory.FactorDepth in
theorem comb_unique {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w w' : Tn t R} (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h')

theorem comb_tan {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w : Tn t R} (h : IsCombAtG t x u a w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb t hu a
  exact comb_unique t hu h2 h ▸ h1


variable {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Lie

end GlobalTheory.FlagEmb
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.Pull

open Cardinal

theorem exists_scf_embedding_dvd :
    ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  intro p V _ _ _ _ hp hpm hV
  let K := FractionRing V
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hK : #K ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors V)).trans hV
  have hx : 1 < ‖algebraMap K C (algebraMap V K p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  obtain ⟨L, hKL, hcl, hac, hL⟩ := GlobalTheory.SmallClosedField.exists_small_closed_subfield hK hx
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  haveI : CharZero K := charZero_of_injective_ringHom (IsFractionRing.injective V K)
  let i : K →+* L := (algebraMap K C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap K C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, ← map_natCast (algebraMap V K), hCp]
  obtain ⟨D, e, he⟩ := GlobalTheory.SmallClosedField.exists_scf_isometry hLp hL
  let g : V →+* D.S := (e.comp i).comp (algebraMap V K)
  have hg : ∀ a : V, ‖g a‖ = ‖algebraMap K C (algebraMap V K a)‖ := fun a => by
    simp only [g, RingHom.comp_apply, he, hi]
  have hle : ∀ a : V, g a ∈ intO D.S := fun a => by
    change ‖g a‖ ≤ 1
    rw [hg]; exact (hC _).2 ⟨a, rfl⟩
  refine ⟨D, g.codRestrict _ hle, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h := congrArg Subtype.val hab
    exact IsFractionRing.injective V K (i.injective (e.injective h))
  · change ‖g a‖ ≤ ‖g b‖ at hab
    rw [hg, hg] at hab
    by_cases hb : b = 0
    · subst hb
      have : algebraMap K C (algebraMap V K a) = 0 := by
        rw [map_zero, map_zero, norm_zero] at hab
        exact norm_le_zero_iff.1 hab
      rw [(map_eq_zero_iff _ (algebraMap K C).injective).1 this |>
        (map_eq_zero_iff _ (IsFractionRing.injective V K)).1]
    · have hb' : algebraMap V K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hb
      have hbC : 0 < ‖algebraMap K C (algebraMap V K b)‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap K C).injective).2 hb')
      obtain ⟨c, hc⟩ := (hC (algebraMap V K a / algebraMap V K b)).1 (by
        rw [map_div₀, norm_div]; exact div_le_one_of_le₀ hab hbC.le)
      refine ⟨c, IsFractionRing.injective V K ?_⟩
      rw [map_mul, hc, mul_div_cancel₀ _ hb']

end GlobalTheory.ShFam.Pad.Pull
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.BCEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {p : ℕ} {W : ValuationSubring ℂ}

section Local

variable {Xo : ∀ l : Level H, Moduli Dw l} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Local

section Global

variable {l : Level H} {c : Coeff l}

theorem exists_isLocalization (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ M : Submonoid (𝓞 c.F), letI := b.toAlgebra; IsLocalization M (c.V W) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨v, -, hv⟩ := GlobalModelGuards.exists_prime_eq c W p hp hW
  haveI hl : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  letI := b.toAlgebra
  refine ⟨v.asIdeal.primeCompl, IsLocalization.isLocalization_of_algEquiv _ (S := v.valuationSubringAtPrime c.F)
    (AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hv)) fun x => ?_)⟩
  exact Subtype.ext (hb x).symm

variable {Xo : Moduli Dw l}

end Global

end GlobalTheory.ShFam.Pad.BCEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.NefFibre

theorem isLB_of_chartPull {Y : Scheme.{0}} {A M : LB Y} (a : ChartPull A M (𝟙 Y)) (hM : M.IsLB)
    (hc : ∀ y : Y, ∃ i, y ∈ A.U i) : A.IsLB := by
  refine GlobalTheory.GenSpread.isLB_of_gm A hc ?_
  intro y i j k hi hj hk
  have hi' : y ∈ M.U (a.idx i) := a.le i hi
  have hj' : y ∈ M.U (a.idx j) := a.le j hj
  have hk' : y ∈ M.U (a.idx k) := a.le k hk
  rw [a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]
  exact gm_cocycle hM (𝟙 Y) y hi' hj' hk'

end GlobalTheory.NefFibre
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.AmpleFibres

theorem relAmple_restrict {S : Scheme.{0}} (U : S.Opens) [IsAffine U.toScheme] (B : Over S) {L : LB B.left}
    (hL : L.IsLB)
    (h : ReciprocityTheory.ChartRestriction.G.Out.RelAmple ((Over.pullback U.ι).obj B) (L.pull (pullback.fst B.hom U.ι))) :
    ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk (B.hom ∣_ U)) (L.pull (B.hom ⁻¹ᵁ U).ι) := by
  have hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst B.hom U
  have hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom
      ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι)
      ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv) := by
    exact GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm
  exact GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h

end GlobalTheory.AmpleFibres
end
